open Lexing

let rec tokens filename (lexbuf : lexbuf) :
    Lexer.token Asai.Range.located list =
  let loc = Asai.Range.of_lexbuf ~source:(`File filename) lexbuf in
  let tok = Lexer.token lexbuf in
  Eio.traceln "%s" ([%show: Lexer.token] tok);
  match tok with
  | EOF -> []
  | _ -> (Asai.Range.locate loc tok) :: tokens filename lexbuf

let catcher f lexbuf =
  try f lexbuf with
   (* | Grammar.Error ->
       let loc = Asai.Range.of_lexbuf lexbuf in
       Reporter.fatalf ~loc Parse_error "failed to parse `%s`"
         (Lexing.lexeme lexbuf) *)
   | Lexer.SyntaxError token ->
       let loc = Asai.Range.of_lexbuf lexbuf in
       Reporter.fatalf ~loc Parse_error "unrecognized token `%s`"
       @@ String.escaped token

type preterm =
    | Universe
and pretype = preterm
and binding = string * pretype
[@@deriving show]

type top =
  | Let of string * binding list * pretype  * preterm
[@@deriving show]

let ident () : string =
  let located_tok = Combinator.next_token () in
  match located_tok.value with
  | Lexer.IDENT name -> name
  | tok->
    let loc = Option.get located_tok.loc in
    Reporter.fatalf ~loc Parse_error "expected <identifier>, but got `%s`" ([%show: Lexer.token] tok)

let parse_let () : top =
  Combinator.consume Lexer.LET;
  let name = ident () in
  Let (name, [], Universe, Universe)

let parse_channel filename ch =
  Reporter.tracef "when parsing file `%s`" filename @@ fun () ->
  let lexbuf = Lexing.from_channel ch in
  lexbuf.lex_curr_p <- { lexbuf.lex_curr_p with pos_fname = filename };
  (* catcher (tokens filename) lexbuf *)
  let top = Combinator.run filename lexbuf (parse_let) in
  Eio.traceln "top level: %s" ([%show : top] top);
  top

let parse_file filename =
  let ch = open_in filename in
  Fun.protect ~finally:(fun _ -> close_in ch) @@ fun _ ->
  parse_channel filename ch
