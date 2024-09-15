open Lexing
open Effect
open Effect.Deep

type _ Effect.t += Next : Lexer.token Asai.Range.located Effect.t
                 | Shift : position -> unit Effect.t
                 | CurrentPosition : position Effect.t

let next_token ()  = perform Next
let shift pos = perform (Shift pos)
let current_position () : position = perform CurrentPosition
let peek_token ()  = 
  let pos = current_position () in
  let tok = next_token () in
  shift pos;
  tok

let consume (predict : Lexer.token) : unit =
  let tok = next_token () in
  if tok.value == predict then
    ()
  else
    let loc = Option.get tok.loc in
    Reporter.fatalf ~loc Parse_error "expected `%s`, but got `%s`"
      ([%show: Lexer.token] predict)
      ([%show: Lexer.token] tok.value)

let run (filename : string) (lexbuf : lexbuf) (f : unit -> 'a) : 'a = 
  try_with f ()
  { effc = fun (type a) (eff: a t) ->
    match eff with
    | Next -> Some (fun (k: (a,_) continuation) -> 
      let tok = Lexer.token lexbuf in
      let loc = Asai.Range.of_lexbuf ~source:(`File filename) lexbuf in
      let tok = (Asai.Range.locate loc tok)in
      continue k tok)
    | Shift pos -> Some (fun k -> set_position lexbuf pos; continue k ())
    | CurrentPosition -> Some (fun k -> continue k lexbuf.lex_curr_p)
    | _ -> None
  }

let (>>) (p1 : unit -> 'a) (p2 : 'a -> 'b) : 'b =
  let a = p1 () in
  p2 a

