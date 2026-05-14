{
exception SyntaxError of string

type token =
  | DATA [@printer fun fmt () -> fprintf fmt "data"]
  | LET [@printer fun fmt () -> fprintf fmt "let"]
  | IMPORT [@printer fun fmt () -> fprintf fmt "import"]
  | UNIVERSE [@printer fun fmt () -> fprintf fmt "universe"]
  | WHERE [@printer fun fmt () -> fprintf fmt "where"]
  | OPEN [@printer fun fmt () -> fprintf fmt "open"]
  | ASSIGN [@printer fun fmt () -> fprintf fmt ":="]
  | ARROW [@printer fun fmt () -> fprintf fmt "->"]
  | STACK_ARROW [@printer fun fmt () -> fprintf fmt "<="]
  | FAT_ARROW [@printer fun fmt () -> fprintf fmt "=>"]
  | COLON [@printer fun fmt () -> fprintf fmt ":"]
  | LAMBDA [@printer fun fmt () -> fprintf fmt "\\"]
  | DOT [@printer fun fmt () -> fprintf fmt "."]
  | SLASH [@printer fun fmt () -> fprintf fmt "/"]
  | VERT [@printer fun fmt () -> fprintf fmt "|"]
  | JOIN [@printer fun fmt () -> fprintf fmt "\xe2\x8a\x94"]
  | L_PAREN [@printer fun fmt () -> fprintf fmt "("]
  | R_PAREN [@printer fun fmt () -> fprintf fmt ")"]
  | L_BRACKET [@printer fun fmt () -> fprintf fmt "{"]
  | R_BRACKET [@printer fun fmt () -> fprintf fmt "}"]
  | QMARK [@printer fun fmt () -> fprintf fmt "?"]
  | IDENT of string [@printer fun fmt name -> fprintf fmt "<identifier:%s>" name]
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
  | "universe" { return lexbuf @@ UNIVERSE }
  | "where" { return lexbuf @@ WHERE }
  | "open" { return lexbuf @@ OPEN }
  | "data" { return lexbuf @@ DATA }
  | "let" { return lexbuf @@ LET }
  | "import" { return lexbuf @@ IMPORT }
  | ":=" { return lexbuf @@ ASSIGN }
  | "->" { return lexbuf @@ ARROW }
  | "<=" { return lexbuf @@ STACK_ARROW }
  | "=>" { return lexbuf @@ FAT_ARROW }
  | ':' { return lexbuf @@ COLON }
  | "\\" { return lexbuf @@ LAMBDA }
  | '.' { return lexbuf @@ DOT }
  | '/' { return lexbuf @@ SLASH }
  | '|' { return lexbuf @@ VERT }
  | "⊔" { return lexbuf @@ JOIN }
  | '(' { return lexbuf @@ L_PAREN }
  | ')' { return lexbuf @@ R_PAREN }
  | '{' { return lexbuf @@ L_BRACKET }
  | '}' { return lexbuf @@ R_BRACKET }
  | '?' { return lexbuf @@ QMARK }
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
