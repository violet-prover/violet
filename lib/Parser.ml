open Lexing

let ident () : string =
  let located_tok = Combinator.next_token () in
  match located_tok.value with
  | Lexer.IDENT name -> name
  | tok->
    let loc = Option.get located_tok.loc in
    Reporter.fatalf ~loc Parse_error "expected <identifier>, but got `%s`" ([%show: Lexer.token] tok)

let parse_let () : Syntax.top =
  Combinator.consume Lexer.LET;
  let name = ident () in
  Let (name, [], Universe, Universe)

let parse_channel filename ch =
  Reporter.tracef "when parsing file `%s`" filename @@ fun () ->
  let lexbuf = Lexing.from_channel ch in
  lexbuf.lex_curr_p <- { lexbuf.lex_curr_p with pos_fname = filename };
  let top = Combinator.run filename lexbuf (parse_let) in
  Eio.traceln "top level: %s" ([%show : Syntax.top] top);
  top

let parse_file filename =
  let ch = open_in filename in
  Fun.protect ~finally:(fun _ -> close_in ch) @@ fun _ ->
  parse_channel filename ch
