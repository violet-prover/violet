{
exception SyntaxError of string

type token =
    COMMA
  | DATA
  | IDENT of string
  | EOF
  [@@deriving show]
    
    let ident str = IDENT str
    let illegal str = raise @@ SyntaxError str
    let return _lexbuf tok = tok
}

let digit = ['0'-'9']
let alpha = ['a'-'z' 'A'-'Z']
let ident = (alpha) (alpha|digit|'_'|'-')*
let whitespace = [' ' '\t']+
let newline = '\r' | '\n' | "\r\n"

rule token =
  parse
  | "#" { comment lexbuf }
  | "data" { return lexbuf @@ DATA }
  | ',' { return lexbuf @@ COMMA }
  | ident { return lexbuf @@ ident (Lexing.lexeme lexbuf) }
  | whitespace { token lexbuf }
  | newline { Lexing.new_line lexbuf; token lexbuf }
  | eof { EOF }
  | _ { illegal @@ Lexing.lexeme lexbuf }

and comment =
  parse
  | newline { Lexing.new_line lexbuf; token lexbuf }
  | eof { EOF }
  | _ { comment lexbuf }
