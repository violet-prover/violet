open Effect
open Effect.Deep

type _ Effect.t += Next : Lexer.token Asai.Range.located Effect.t
                 | Shift : Lexing.position -> unit Effect.t
                 | CurrentPosition : Lexing.position Effect.t

let next_token ()  = perform Next
let shift pos = perform (Shift pos)
let current_position () : Lexing.position = perform CurrentPosition

let run (filename : string) (lexbuf : Lexing.lexbuf) (f : unit -> 'a) : 'a = 
  try_with f ()
  { effc = fun (type a) (eff: a t) ->
    match eff with
    | Next -> Some (fun (k: (a,_) continuation) -> 
      let tok = Lexer.token lexbuf in
      let loc = Asai.Range.of_lexbuf ~source:(`File filename) lexbuf in
      let tok = (Asai.Range.locate loc tok) in
      continue k tok)
    | Shift pos -> Some (fun k -> Lexing.set_position lexbuf pos; continue k ())
    | CurrentPosition -> Some (fun k -> continue k lexbuf.lex_curr_p)
    | _ -> None
  }

let consume (predict : Lexer.token) : unit =
  let tok = next_token () in
  if tok.value == predict then
    ()
  else
    let loc = Option.get tok.loc in
    Reporter.fatalf ~loc Parse_error "expected `%s`, but got `%s`"
      ([%show: Lexer.token] predict)
      ([%show: Lexer.token] tok.value)

let many (p : unit -> 'a) : 'a list =
  let res = ref [] in
  let quit_loop = ref false in
  while not !quit_loop do
    let pos = current_position () in
    try
      let x = p () in
      res := x :: !res
    with | _ -> shift pos; quit_loop := true
  done;
  !res
let (<|>) (p1 : unit -> 'a) (p2 : unit -> 'a) () : 'a =
  let pos = current_position () in
  let x = (try p1 () with | _ ->
    shift pos; p2 ()) in
  x
