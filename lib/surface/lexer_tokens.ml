(* Re-run the lexer purely to recover a token stream with byte spans, for
   syntax highlighting (literate weave). The parser proper drives the lexer
   through its own buffered token reader; this is a separate, side-effect-free
   pass that does not feed the parser. *)

type spanned =
  { token : Lexer.token
  ; start_offset : int (* byte offset of the lexeme start *)
  ; end_offset : int (* byte offset just past the lexeme *)
  }

let tokens_with_spans (src : string) : spanned list =
  let lexbuf = Lexing.from_string src in
  let rec loop acc =
    match Lexer.token lexbuf with
    | Lexer.EOF -> List.rev acc
    | token ->
      let start_offset = Lexing.lexeme_start lexbuf in
      let end_offset = Lexing.lexeme_end lexbuf in
      loop ({ token; start_offset; end_offset } :: acc)
  in
  loop []
;;
