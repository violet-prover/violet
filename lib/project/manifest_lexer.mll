{
type token =
  | NAME       (* \name *)
  | VERSION    (* \version *)
  | DEP        (* \dep *)
  | LOCKED     (* \locked *)
  | LITERATE   (* \literate *)
  | IDENT of string
  | STRING of string
  | LPAREN
  | RPAREN
  | COMMA
  | EQUALS
  | EOF
[@@deriving show]

exception SyntaxError of string

let strip_quotes s =
  let n = String.length s in
  if n >= 2 then String.sub s 1 (n - 2) else s
;;
}

let ws    = [' ' '\t' '\r' '\n']
let alpha = ['a'-'z' 'A'-'Z' '_']
let ident_char = alpha | ['0'-'9' '-']

rule token = parse
  | ws+              { token lexbuf }
  | "#" [^ '\n']*    { token lexbuf }                       (* line comment *)
  | "\\name"         { NAME }
  | "\\version"      { VERSION }
  | "\\dep"          { DEP }
  | "\\locked"       { LOCKED }
  | "\\literate"     { LITERATE }
  | "("              { LPAREN }
  | ")"              { RPAREN }
  | ","              { COMMA }
  | "="              { EQUALS }
  | '"' [^ '"']* '"' { STRING (strip_quotes (Lexing.lexeme lexbuf)) }
  | alpha ident_char* { IDENT (Lexing.lexeme lexbuf) }
  | eof              { EOF }
  | _ as c           { raise (SyntaxError (Printf.sprintf "unexpected character %C" c)) }
