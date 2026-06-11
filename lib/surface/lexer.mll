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
  | AXIOM [@printer fun fmt () -> fprintf fmt "\\axiom"]
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
(* UTF-8 byte ranges treated as identifier letters.

   utf8_letter_2 — U+0080–U+07FF: Latin Extended, IPA, Greek (α λ Λ),
     Cyrillic, Hebrew, Arabic. UTF-8 lead 0xC2–0xDF.
   utf8_letter_3 — U+2100–U+217F Letter-like Symbols (ℂ ℕ ℝ ℤ ℚ ℋ ℓ).
     UTF-8 lead 0xE2, second byte 0x84–0x85.
   utf8_letter_4 — U+1D400–U+1D7FF Mathematical Alphanumeric Symbols
     (𝓤 𝒰 𝒜 𝔸 𝕊). UTF-8 lead 0xF0 0x9D, third byte 0x90–0x9F. *)
let utf8_letter_2 = ['\194'-'\223'] ['\128'-'\191']
let utf8_letter_3 = '\226' ['\132'-'\133'] ['\128'-'\191']
let utf8_letter_4 = '\240' '\157' ['\144'-'\159'] ['\128'-'\191']
let utf8_letter = utf8_letter_2 | utf8_letter_3 | utf8_letter_4
let alpha = ['a'-'z' 'A'-'Z'] | utf8_letter
let ident = (alpha) (alpha|digit|'_'|'-')*
let whitespace = [' ' '\t']+
let newline = '\r' | '\n' | "\r\n"
(* Symbol units. Each alternative is a complete UTF-8 codepoint (or one ASCII
   symbol byte) so that sym_unit+ partitions cleanly at codepoint boundaries
   and doesn't absorb the letter ranges above. Reserved Unicode tokens like
   `⊔` still win via first-rule precedence on equal-length matches. *)
let ascii_sym = ['+' '-' '*' '/' '<' '>' '=' '!' '&' '^' '?' '%' '@' '$' ',']
(* 3-byte UTF-8 minus the Letter-like Symbols block (0xE2 0x84/0x85 xx). *)
let utf8_sym_3 =
    ['\224'-'\225'] ['\128'-'\191'] ['\128'-'\191']
  | '\226' (['\128'-'\131'] | ['\134'-'\191']) ['\128'-'\191']
  | ['\227'-'\239'] ['\128'-'\191'] ['\128'-'\191']
(* 4-byte UTF-8 minus the Math Alphanumeric block (0xF0 0x9D 0x90–0x9F xx). *)
let utf8_sym_4 =
    '\240' (['\128'-'\156'] | ['\158'-'\191']) ['\128'-'\191'] ['\128'-'\191']
  | '\240' '\157' (['\128'-'\143'] | ['\160'-'\191']) ['\128'-'\191']
  | ['\241'-'\244'] ['\128'-'\191'] ['\128'-'\191'] ['\128'-'\191']
let sym_unit = ascii_sym | utf8_sym_3 | utf8_sym_4

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
  | "\\axiom" { return lexbuf @@ AXIOM }
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
  | '_' { return lexbuf @@ IDENT "_" }
  | sym_unit+ { return lexbuf @@ SYMBOL (Lexing.lexeme lexbuf) }
  | whitespace { token lexbuf }
  | newline { Lexing.new_line lexbuf; token lexbuf }
  | eof { EOF }
  | _ { illegal @@ Lexing.lexeme lexbuf }

and comment =
  parse
  | newline { Lexing.new_line lexbuf; token lexbuf }
  | eof { EOF }
  | _ { comment lexbuf }
