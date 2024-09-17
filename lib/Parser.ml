open Lexing
open Syntax

let parens (p : unit -> 'a) () : 'a =
  Combinator.consume Lexer.L_PAREN;
  let x = p () in
  Combinator.consume Lexer.R_PAREN;
  x

let bracket (p : unit -> 'a) () : 'a =
  Combinator.consume Lexer.L_BRACKET;
  let x = p () in
  Combinator.consume Lexer.R_BRACKET;
  x

let ident () : string =
  let located_tok = Combinator.next_token () in
  match located_tok.value with
  | Lexer.IDENT name -> name
  | tok ->
      let loc = Option.get located_tok.loc in
      Reporter.fatalf ~loc Parse_error "expected <identifier>, but got `%s`"
        ([%show: Lexer.token] tok)

let rec p_preterm () : Surface.preterm =
  let a = p_patom () in
  let args = Combinator.many p_arg () in
  List.fold_left
    (fun a (arg : Surface.as_arg) -> Surface.App (arg.implicit, a, arg.term))
    a args

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
  let pos = Combinator.current_position () in
  let tok = Combinator.next_token () in
  let loc = Option.get tok.loc in
  let tm : Surface.preterm =
    match tok.value with
    | Lexer.UNIV -> Universe
    | Lexer.IDENT s -> Var s
    (* 用括號包住的 term 也能當成一種 atom 使用 *)
    | _ ->
        Combinator.shift pos;
        (parens p_preterm) ()
  in
  Located (Asai.Range.locate loc tm)

(* name : preterm *)
let p_binding (implicit : bool) () : Surface.preterm binder =
  let name = ident () in
  Combinator.consume Lexer.COLON;
  let tm = p_preterm () in
  { name; bound = tm; implicit }

let p_let () : Surface.top =
  let open Combinator in
  consume Lexer.LET;
  let name = ident () in
  let bindings =
    many (bracket (p_binding true) <|> parens (p_binding false)) ()
  in
  consume Lexer.COLON;
  let ty = p_preterm () in
  consume Lexer.ASSIGN;
  let tm = p_preterm () in
  Let (name, bindings, ty, tm)

let p_top () : Surface.top Asai.Range.located =
  let loc = Combinator.current_loc () in
  let value = p_let () in
  { loc; value }

let p_all (name : string) () : Surface.t =
  (* FIXME: this is wrong, a top failed should get a reason
     then seek next start token & continue parsing,
     which is not many intend todo.
  *)
  let tops = Combinator.many p_top () in
  Combinator.consume Lexer.EOF;
  { name; tops }

let rec tokens filename lexbuf =
  let tok = Lexer.token lexbuf in
  let loc = Asai.Range.of_lexbuf ~source:(`File filename) lexbuf in
  match tok with
  | EOF -> Asai.Range.locate loc tok :: []
  | tok -> Asai.Range.locate loc tok :: tokens filename lexbuf

let parse_channel filename ch =
  Reporter.tracef "when parsing file `%s`" filename @@ fun () ->
  let lexbuf = Lexing.from_channel ch in
  lexbuf.lex_curr_p <- { lexbuf.lex_curr_p with pos_fname = filename };
  Combinator.run (tokens filename lexbuf) (p_all filename)

let parse_file filename =
  let ch = open_in filename in
  Fun.protect ~finally:(fun _ -> close_in ch) @@ fun _ ->
  parse_channel filename ch
