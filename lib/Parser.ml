open Lexing
open Syntax

let ident () : string =
  let located_tok = Combinator.next_token () in
  match located_tok.value with
  | Lexer.IDENT name -> name
  | tok ->
    let loc = Option.get located_tok.loc in
    Reporter.fatalf ~loc Parse_error "expected <identifier>, but got `%s`" ([%show: Lexer.token] tok)
  
let p_pretype () : pretype =
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
  let typ = p_pretype ()  in
  (name, typ)

let p_let () : top =
  let open Combinator in
  consume Lexer.LET;
  let name = ident () in
  let bindings = many ((bracket p_binding) <|> (parens p_binding)) in
  Let (name, bindings, Universe, Universe)

let rec tokens filename lexbuf : Lexer.token Asai.Range.located list =
  let tok = Lexer.token lexbuf in
  match tok with
  | EOF -> []
  | tok ->
    let loc = Asai.Range.of_lexbuf ~source:(`File filename) lexbuf in
    let tok = Asai.Range.locate loc tok in
    tok :: tokens filename lexbuf

let parse_channel filename ch =
  Reporter.tracef "when parsing file `%s`" filename @@ fun () ->
  let lexbuf = Lexing.from_channel ch in
  lexbuf.lex_curr_p <- { lexbuf.lex_curr_p with pos_fname = filename };
  let stream = tokens filename lexbuf in
  let top = Combinator.run stream (p_let) in
  Eio.traceln "top level: %s" ([%show : top] top);
  top

let parse_file filename =
  let ch = open_in filename in
  Fun.protect ~finally:(fun _ -> close_in ch) @@ fun _ ->
  parse_channel filename ch
