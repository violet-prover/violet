open Lexing
open Syntax

let ident () : string =
  let located_tok = Combinator.next_token () in
  match located_tok.value with
  | Lexer.IDENT name -> name
  | tok ->
    let loc = Option.get located_tok.loc in
    Reporter.fatalf ~loc Parse_error "expected <identifier>, but got `%s`" ([%show: Lexer.token] tok)
  
let p_preterm () : preterm =
  let located_tok = Combinator.next_token () in
  match located_tok.value with
  | Lexer.UNIV -> Universe
  | Lexer.IDENT s -> Var s
  | tok ->
    let loc = Option.get located_tok.loc in
    Reporter.fatalf ~loc Parse_error "expected <type>, but got `%s`" ([%show: Lexer.token] tok)

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

(* name : pretype *)
let p_binding () : binding =
  let name = ident () in
  Combinator.consume Lexer.COLON;
  let typ = p_preterm ()  in
  (name, typ)

let p_let () : top =
  let open Combinator in
  consume Lexer.LET;
  let name = ident () in
  let bindings = many ((bracket p_binding) <|> (parens p_binding)) () in
  consume Lexer.COLON;
  let ty = p_preterm () in
  consume Lexer.ASSIGN;
  let tm = p_preterm () in
  Let (name, bindings, ty, tm)

let p_top : unit -> top =
  p_let

let p_all (name : string) () : Syntax.t =
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
  | EOF ->
    (Asai.Range.locate loc tok) :: []
  | tok ->
    (Asai.Range.locate loc tok) :: tokens filename lexbuf

let parse_channel filename ch =
  Reporter.tracef "when parsing file `%s`" filename @@ fun () ->
  let lexbuf = Lexing.from_channel ch in
  lexbuf.lex_curr_p <- { lexbuf.lex_curr_p with pos_fname = filename };
  Combinator.run (tokens filename lexbuf) (p_all filename)

let parse_file filename =
  let ch = open_in filename in
  Fun.protect ~finally:(fun _ -> close_in ch) @@ fun _ ->
  parse_channel filename ch
