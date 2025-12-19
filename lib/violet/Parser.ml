open Lexing
open Syntax
open Yuujinchou

let parens (p : unit -> 'a) () : 'a =
  Combinator.consume Lexer.L_PAREN;
  let x = p () in
  Combinator.consume Lexer.R_PAREN;
  x
;;

let bracket (p : unit -> 'a) () : 'a =
  Combinator.consume Lexer.L_BRACKET;
  let x = p () in
  Combinator.consume Lexer.R_BRACKET;
  x
;;

let ident () : string =
  let located_tok = Combinator.next_token () in
  match located_tok.value with
  | Lexer.IDENT name -> name
  | tok ->
    let loc = Option.get located_tok.loc in
    Reporter.fatalf
      ~loc
      Parse_error
      "expected <identifier>, but got `%s`"
      ([%show: Lexer.token] tok)
;;

let rec p_preterm () : Surface.preterm = Combinator.infix partial_arrow spine ()

and partial_arrow () : Surface.preterm -> Surface.preterm -> Surface.preterm =
  Combinator.consume Lexer.ARROW;
  fun a b -> Pi ({ name = "_"; bound = a; implicit = false }, b)

and spine () : Surface.preterm =
  let a = p_patom () in
  let args = Combinator.many p_arg () in
  List.fold_left
    (fun a (arg : Surface.as_arg) -> Surface.App (arg.implicit, a, arg.term))
    a
    args

and p_arg () : Surface.as_arg =
  let pos = Combinator.current_position () in
  let tok = Combinator.next_token () in
  match tok.value with
  | Lexer.L_BRACKET ->
    let atom = p_patom () in
    Combinator.consume Lexer.R_BRACKET;
    { implicit = true; term = atom }
  | _ ->
    Combinator.shift pos;
    let atom = p_patom () in
    { implicit = false; term = atom }

and p_patom () : Surface.preterm =
  let open Combinator in
  let pos = current_position () in
  let tok = next_token () in
  let loc = Option.get tok.loc in
  let tm : Surface.preterm =
    match tok.value with
    | Lexer.UNIV -> Universe
    | Lexer.IDENT s -> Var s
    | Lexer.L_PAREN ->
      (match catch_parse_error (p_multi_bindings false) with
       | Some binders ->
         (* good, we got bindings, now parse the rest *)
         consume Lexer.R_PAREN;
         consume Lexer.ARROW;
         let rhs = p_preterm () in
         Surface.pi binders rhs
       | None ->
         (* 用括號包住的 term 也能當成一種 atom 使用 *)
         shift pos;
         (parens p_preterm) ())
    | Lexer.L_BRACKET ->
      shift pos;
      let binders = bracket (p_multi_bindings true) () in
      consume Lexer.ARROW;
      let rhs = p_preterm () in
      Surface.pi binders rhs
    | Lexer.LAMBDA ->
      shift pos;
      consume Lexer.LAMBDA;
      (match catch_parse_error (many1 ident) with
       | Some names ->
         consume Lexer.ARROW;
         let tm = p_preterm () in
         Surface.lambda names tm
       | None ->
         let bindings_lists =
           many (bracket (p_multi_bindings true) <|> parens (p_multi_bindings false)) ()
         in
         let bindings = List.concat bindings_lists in
         consume Lexer.ARROW;
         let tm = p_preterm () in
         Surface.typed_lambda bindings tm)
    | tok ->
      Reporter.fatalf ~loc Parse_error "unexpected token %s" ([%show: Lexer.token] tok)
  in
  Located (Asai.Range.locate loc tm)

(* name1 name2 ... : preterm *)
and p_multi_bindings (implicit : bool) () : Surface.preterm binder list =
  let rec collect_names acc =
    let pos = Combinator.current_position () in
    let tok = Combinator.next_token () in
    match tok.value with
    | Lexer.IDENT name -> collect_names (name :: acc)
    | Lexer.COLON ->
      Combinator.shift pos;
      List.rev acc
    | _ ->
      Combinator.shift pos;
      List.rev acc
  in
  let first_name = ident () in
  let rest_names = collect_names [] in
  Combinator.consume Lexer.COLON;
  let tm = p_preterm () in
  let names = first_name :: rest_names in
  List.map (fun name -> { name; bound = tm; implicit }) names
;;

let p_let () : Surface.top =
  let open Combinator in
  consume Lexer.LET;
  let name = ident () in
  let bindings_lists =
    many (bracket (p_multi_bindings true) <|> parens (p_multi_bindings false)) ()
  in
  let bindings = List.concat bindings_lists in
  consume Lexer.COLON;
  let ty = p_preterm () in
  consume Lexer.ASSIGN;
  let tm = p_preterm () in
  Let (name, bindings, ty, tm)
;;

let p_path () : Trie.path =
  let first = ident () in
  let rest =
    Combinator.many
      (fun () ->
         Combinator.consume Lexer.DOT;
         ident ())
      ()
  in
  first :: rest
;;

let p_ind_clause () : Surface.pretype binder =
  Combinator.consume Lexer.VERT;
  let name = ident () in
  Combinator.consume Lexer.COLON;
  let ty = p_preterm () in
  { implicit = false; name; bound = ty }
;;

let p_inductive () : Surface.top =
  let open Combinator in
  consume Lexer.DATA;
  let name = ident () in
  let params_lists =
    many (bracket (p_multi_bindings true) <|> parens (p_multi_bindings false)) ()
  in
  let params = List.concat params_lists in
  consume Lexer.COLON;
  let ind_ty = p_preterm () in
  let clauses = many p_ind_clause () in
  Data { name; params; ind_ty; clauses }
;;

let p_top () : Surface.top Asai.Range.located =
  let open Combinator in
  let loc = current_loc () in
  let value = (p_let <|> p_inductive) () in
  { loc; value }
;;

let p_import () : Trie.path =
  let open Combinator in
  consume Lexer.IMPORT;
  p_path ()
;;

let p_all (name : string) () : Surface.t =
  let imports = Combinator.many p_import () in
  (* FIXME: this is wrong, a top failed should get a reason
     then seek next start token & continue parsing,
     which is not `many` intend todo.
  *)
  let tops = Combinator.many p_top () in
  Combinator.consume Lexer.EOF;
  { name; imports; tops }
;;

let rec tokens filename lexbuf =
  let tok = Lexer.token lexbuf in
  let loc = Asai.Range.of_lexbuf ~source:(`File filename) lexbuf in
  match tok with
  | EOF -> Asai.Range.locate loc tok :: []
  | tok -> Asai.Range.locate loc tok :: tokens filename lexbuf
;;

let parse_channel filename ch =
  Reporter.tracef "when parsing file `%s`" filename
  @@ fun () ->
  let lexbuf = Lexing.from_channel ch in
  lexbuf.lex_curr_p <- { lexbuf.lex_curr_p with pos_fname = filename };
  Combinator.run (tokens filename lexbuf) (p_all filename)
;;

let parse_file filename =
  let ch = open_in filename in
  Fun.protect ~finally:(fun _ -> close_in ch) @@ fun _ -> parse_channel filename ch
;;
