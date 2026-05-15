{
exception SyntaxError of string

type token =
  | DATA [@printer fun fmt () -> fprintf fmt "\\data"]
  | LET [@printer fun fmt () -> fprintf fmt "\\let"]
  | EXPORT [@printer fun fmt () -> fprintf fmt "\\export"]
  | IMPORT [@printer fun fmt () -> fprintf fmt "\\import"]
  | UNIVERSE [@printer fun fmt () -> fprintf fmt "\\universe"]
  | WHERE [@printer fun fmt () -> fprintf fmt "\\where"]
  | OPERATOR [@printer fun fmt () -> fprintf fmt "\\operator"]
  | OPEN [@printer fun fmt () -> fprintf fmt "\\open"]
  | ELIM [@printer fun fmt () -> fprintf fmt "\\elim"]
  | INTRO [@printer fun fmt () -> fprintf fmt "\\intro"]
  | SPLIT [@printer fun fmt () -> fprintf fmt "\\split"]
  | STRONGER_THAN [@printer fun fmt () -> fprintf fmt "\\stronger_than"]
  | WEAKER_THAN [@printer fun fmt () -> fprintf fmt "\\weaker_than"]
  | SAME_AS [@printer fun fmt () -> fprintf fmt "\\same_as"]
  | ASSOCIATIVITY [@printer fun fmt () -> fprintf fmt "\\associativity"]
  | LEFT [@printer fun fmt () -> fprintf fmt "\\left"]
  | RIGHT [@printer fun fmt () -> fprintf fmt "\\right"]
  | NONE [@printer fun fmt () -> fprintf fmt "\\none"]
  | RECORD [@printer fun fmt () -> fprintf fmt "\\record"]
  | ARROW [@printer fun fmt () -> fprintf fmt "->"]
  | STACK_ARROW [@printer fun fmt () -> fprintf fmt "<="]
  | FAT_ARROW [@printer fun fmt () -> fprintf fmt "=>"]
  | COLON [@printer fun fmt () -> fprintf fmt ":"]
  | LAMBDA [@printer fun fmt () -> fprintf fmt "\\"]
  | SLASH [@printer fun fmt () -> fprintf fmt "/"]
  | VERT [@printer fun fmt () -> fprintf fmt "|"]
  | JOIN [@printer fun fmt () -> fprintf fmt "\xe2\x8a\x94"]
  | L_PAREN [@printer fun fmt () -> fprintf fmt "("]
  | R_PAREN [@printer fun fmt () -> fprintf fmt ")"]
  | L_BRACKET [@printer fun fmt () -> fprintf fmt "{"]
  | R_BRACKET [@printer fun fmt () -> fprintf fmt "}"]
  | QMARK [@printer fun fmt () -> fprintf fmt "?"]
  | DOT [@printer fun fmt () -> fprintf fmt "."]
  | IDENT of string [@printer fun fmt name -> fprintf fmt "<identifier:%s>" name]
  | SYMBOL of string [@printer fun fmt s -> fprintf fmt "<symbol:%s>" s]
  | STRING of string [@printer fun fmt s -> fprintf fmt "<string:%s>" s]
  | EOF
[@@deriving show]

let ident str = IDENT str
let illegal str = raise @@ SyntaxError str
let return _lexbuf tok = tok

(* Strip the leading '"' and trailing '"' of a lexeme like `"abc"`. *)
let strip_quotes s =
  let n = String.length s in
  if n >= 2 then String.sub s 1 (n - 2) else s
;;
}

let digit = ['0'-'9']
let alpha = ['a'-'z' 'A'-'Z']
let ident = (alpha) (alpha|digit|'_'|'-')*
let whitespace = [' ' '\t']+
let newline = '\r' | '\n' | "\r\n"
let sym_char = ['+' '-' '*' '/' '<' '>' '=' '!' '&' '^' '?' '%' '@' '$' ',']

rule token =
  parse
  | "#" { comment lexbuf }
  (* Reserved punctuation/keyword sequences are listed before the generic
     SYMBOL rule. ocamllex uses longest-match, then first-rule-wins on ties,
     so reserved 2-3 char sequences still win against single-char SYMBOL,
     and longer SYMBOL runs (e.g. `->>`) win against shorter reserved ones. *)
  (* Backslash-prefixed keywords. Listed before the bare `"\\"` LAMBDA rule
     so longest-match selects the keyword form when applicable. *)
  | "\\universe" { return lexbuf @@ UNIVERSE }
  | "\\where" { return lexbuf @@ WHERE }
  | "\\open" { return lexbuf @@ OPEN }
  | "\\data" { return lexbuf @@ DATA }
  | "\\let" { return lexbuf @@ LET }
  | "\\export" { return lexbuf @@ EXPORT }
  | "\\import" { return lexbuf @@ IMPORT }
  | "\\operator" { return lexbuf @@ OPERATOR }
  | "\\elim" { return lexbuf @@ ELIM }
  | "\\intro" { return lexbuf @@ INTRO }
  | "\\split" { return lexbuf @@ SPLIT }
  | "\\stronger_than" { return lexbuf @@ STRONGER_THAN }
  | "\\weaker_than" { return lexbuf @@ WEAKER_THAN }
  | "\\same_as" { return lexbuf @@ SAME_AS }
  | "\\associativity" { return lexbuf @@ ASSOCIATIVITY }
  | "\\left" { return lexbuf @@ LEFT }
  | "\\right" { return lexbuf @@ RIGHT }
  | "\\none" { return lexbuf @@ NONE }
  | "\\record" { return lexbuf @@ RECORD }
  | "->" { return lexbuf @@ ARROW }
  | "<=" { return lexbuf @@ STACK_ARROW }
  | "=>" { return lexbuf @@ FAT_ARROW }
  | ':' { return lexbuf @@ COLON }
  | "\\" { return lexbuf @@ LAMBDA }
  | '/' { return lexbuf @@ SLASH }
  | '|' { return lexbuf @@ VERT }
  | "⊔" { return lexbuf @@ JOIN }
  | '(' { return lexbuf @@ L_PAREN }
  | ')' { return lexbuf @@ R_PAREN }
  | '{' { return lexbuf @@ L_BRACKET }
  | '}' { return lexbuf @@ R_BRACKET }
  | '?' { return lexbuf @@ QMARK }
  | '.' { return lexbuf @@ DOT }
  | '"' ([^ '"' '\n']* as s) '"' { return lexbuf @@ STRING s }
  | ident { return lexbuf @@ ident (Lexing.lexeme lexbuf) }
  | sym_char+ { return lexbuf @@ SYMBOL (Lexing.lexeme lexbuf) }
  | whitespace { token lexbuf }
  | newline { Lexing.new_line lexbuf; token lexbuf }
  | eof { EOF }
  | _ { illegal @@ Lexing.lexeme lexbuf }

and comment =
  parse
  | newline { Lexing.new_line lexbuf; token lexbuf }
  | eof { EOF }
  | _ { comment lexbuf }
