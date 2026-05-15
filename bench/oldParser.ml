(* Legacy combinator parser, kept here so test_typed_parser can benchmark and
   AST-compare against the typed-algebraic parser. Not used in production. *)

open Yuujinchou
open Violet_kernel.Syntax
module Surface = Violet_elab.Surface
module Lexer = Violet_elab.Lexer
module Reporter = Violet_elab.Reporter

module Tokens = struct
  type t = Lexer.token Asai.Range.located list
end

module TokenState = Algaeff.State.Make (Tokens)

exception Impossible

let next_token () =
  match TokenState.get () with
  | [ eof ] -> eof
  | tok :: buf ->
    TokenState.set buf;
    tok
  | [] -> raise Impossible
;;

let shift pos = TokenState.set pos
let current_position () = TokenState.get ()

let run (init : Lexer.token Asai.Range.located list) (f : unit -> 'a) : 'a =
  TokenState.run ~init @@ fun () -> f ()
;;

let current_loc () : Asai.Range.t option =
  let pos = current_position () in
  let tok = next_token () in
  shift pos;
  tok.loc
;;

let consume (predict : Lexer.token) : unit =
  let tok = next_token () in
  if tok.value == predict
  then ()
  else (
    let loc = Option.get tok.loc in
    Reporter.fatalf
      ~loc
      Parse_error
      "expected `%s`, but got `%s`"
      ([%show: Lexer.token] predict)
      ([%show: Lexer.token] tok.value))
;;

let catch_parse_error (p : unit -> 'a) : 'a option =
  let pos = current_position () in
  Reporter.try_with
    ~fatal:(fun d ->
      match d.message with
      | Parse_error ->
        shift pos;
        None
      | _ -> Reporter.fatal_diagnostic d)
    (fun () -> Some (p ()))
;;

let rec many (p : unit -> 'a) () : 'a list =
  let x = catch_parse_error p in
  match x with
  | None -> []
  | Some x -> x :: many p ()
;;

let many1 (p : unit -> 'a) () : 'a list =
  let first = p () in
  first :: many p ()
;;

let ( <|> ) (p1 : unit -> 'a) (p2 : unit -> 'a) () : 'a =
  match catch_parse_error p1 with
  | None -> p2 ()
  | Some x -> x
;;

let rec infix (op : unit -> 'a -> 'a -> 'a) (tm : unit -> 'a) () : 'a =
  let lhs = tm () in
  match catch_parse_error op with
  | Some bin ->
    let rhs = infix op tm () in
    bin lhs rhs
  | None -> lhs
;;

let parens (p : unit -> 'a) () : 'a =
  consume Lexer.L_PAREN;
  let x = p () in
  consume Lexer.R_PAREN;
  x
;;

let bracket (p : unit -> 'a) () : 'a =
  consume Lexer.L_BRACKET;
  let x = p () in
  consume Lexer.R_BRACKET;
  x
;;

let ident () : string =
  let located_tok = next_token () in
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

let rec p_preterm () : Surface.preterm = infix partial_arrow p_max_level ()

and partial_arrow () : Surface.preterm -> Surface.preterm -> Surface.preterm =
  consume Lexer.ARROW;
  fun a b -> Pi ({ name = "_"; bound = a; implicit = false }, b)

and p_max_level () : Surface.preterm = infix partial_join spine ()

and partial_join () : Surface.preterm -> Surface.preterm -> Surface.preterm =
  consume Lexer.JOIN;
  fun a b -> Max (a, b)

and spine () : Surface.preterm =
  let a = p_patom () in
  let args = many p_arg () in
  List.fold_left
    (fun a (arg : Surface.as_arg) -> Surface.App (arg.implicit, a, arg.term))
    a
    args

and p_arg () : Surface.as_arg =
  let pos = current_position () in
  let tok = next_token () in
  match tok.value with
  | Lexer.L_BRACKET ->
    let atom = p_patom () in
    consume Lexer.R_BRACKET;
    { implicit = true; term = atom }
  | _ ->
    shift pos;
    let atom = p_patom () in
    { implicit = false; term = atom }

and p_patom () : Surface.preterm =
  let pos = current_position () in
  let tok = next_token () in
  let loc = Option.get tok.loc in
  let tm : Surface.preterm =
    match tok.value with
    | Lexer.IDENT s -> Var [ s ]
    | Lexer.L_PAREN ->
      (match catch_parse_error (p_multi_bindings false) with
       | Some binders ->
         consume Lexer.R_PAREN;
         consume Lexer.ARROW;
         let rhs = p_preterm () in
         Surface.pi binders rhs
       | None ->
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

and p_multi_bindings (implicit : bool) () : Surface.preterm Surface.binder list =
  let rec collect_names acc =
    let pos = current_position () in
    let tok = next_token () in
    match tok.value with
    | Lexer.IDENT name -> collect_names (name :: acc)
    | Lexer.COLON ->
      shift pos;
      List.rev acc
    | _ ->
      shift pos;
      List.rev acc
  in
  let first_name = ident () in
  let rest_names = collect_names [] in
  consume Lexer.COLON;
  let tm = p_preterm () in
  let names = first_name :: rest_names in
  List.map (fun name -> { name; bound = tm; implicit }) names
;;

let p_let () : Surface.top =
  consume Lexer.LET;
  let name = ident () in
  let bindings_lists =
    many (bracket (p_multi_bindings true) <|> parens (p_multi_bindings false)) ()
  in
  let bindings = List.concat bindings_lists in
  consume Lexer.COLON;
  let ty = p_preterm () in
  consume Lexer.FAT_ARROW;
  let tm = p_preterm () in
  Let (name, bindings, ty, tm)
;;

let p_path () : Trie.path =
  let first = ident () in
  let rest =
    many
      (fun () ->
         consume Lexer.DOT;
         ident ())
      ()
  in
  first :: rest
;;

let p_ind_clause () : Surface.pretype Surface.binder =
  consume Lexer.VERT;
  let name = ident () in
  consume Lexer.COLON;
  let ty = p_preterm () in
  { implicit = false; name; bound = ty }
;;

let p_inductive () : Surface.top =
  consume Lexer.DATA;
  let name = ident () in
  let params_lists =
    many (bracket (p_multi_bindings true) <|> parens (p_multi_bindings false)) ()
  in
  let params = List.concat params_lists in
  consume Lexer.COLON;
  let ret = p_preterm () in
  let ctors = many p_ind_clause () in
  Data
    { name; params; deps = Surface.telescope ret; ind_ty = Surface.codomain ret; ctors }
;;

let p_universe () : Surface.top =
  consume Lexer.UNIVERSE;
  let first = ident () in
  let rest = many ident () in
  Universe_decl (first :: rest)
;;

let p_top () : Surface.top Asai.Range.located =
  let loc = current_loc () in
  let value = (p_let <|> p_inductive <|> p_universe) () in
  { loc; value }
;;

let p_import () : Trie.path =
  consume Lexer.IMPORT;
  p_path ()
;;

let p_all (name : string) () : Surface.t =
  let imports = many p_import () in
  let tops = many p_top () in
  consume Lexer.EOF;
  { name; imports; tops }
;;

let rec tokens filename lexbuf =
  let tok = Lexer.token lexbuf in
  let loc = Asai.Range.of_lexbuf ~source:(`File filename) lexbuf in
  match tok with
  | Lexer.EOF -> [ Asai.Range.locate loc tok ]
  | _ -> Asai.Range.locate loc tok :: tokens filename lexbuf
;;

let parse_file filename =
  let ch = open_in filename in
  Fun.protect ~finally:(fun _ -> close_in ch)
  @@ fun _ ->
  let lexbuf = Lexing.from_channel ch in
  lexbuf.Lexing.lex_curr_p
  <- { lexbuf.Lexing.lex_curr_p with Lexing.pos_fname = filename };
  let toks = tokens filename lexbuf in
  run toks (p_all filename)
;;
