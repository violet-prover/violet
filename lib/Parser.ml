open Lexing

let rec parser filename (lexbuf : lexbuf) :
    Lexer.token Asai.Range.located list =
  let loc = Asai.Range.of_lexbuf ~source:(`File filename) lexbuf in
  let tok = Lexer.token lexbuf in
  Eio.traceln "%s" ([%show: Lexer.token] tok);
  match tok with
  | EOF -> []
  | _ -> (Asai.Range.locate loc tok) :: parser filename lexbuf

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

let parse_channel filename ch =
  Reporter.tracef "when parsing file `%s`" filename @@ fun () ->
  let lexbuf = Lexing.from_channel ch in
  lexbuf.lex_curr_p <- { lexbuf.lex_curr_p with pos_fname = filename };
  catcher (parser filename) lexbuf

let parse_file filename =
  let ch = open_in filename in
  Fun.protect ~finally:(fun _ -> close_in ch) @@ fun _ ->
  parse_channel filename ch
