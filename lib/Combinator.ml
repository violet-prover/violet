open Effect
open Effect.Deep

type _ Effect.t += Next : Lexer.token Asai.Range.located Effect.t
                 | Shift : Lexer.token Asai.Range.located list -> unit Effect.t
                 | CurrentPosition :  Lexer.token Asai.Range.located list Effect.t

let next_token ()  = perform Next
let shift pos = perform (Shift pos)
let current_position () = perform CurrentPosition

let run (init : Lexer.token Asai.Range.located list) (f : unit -> 'a) : 'a = 
  let internal = ref init in
  try_with f ()
  { effc = fun (type a) (eff: a t) ->
    match eff with
    | Next -> Some (fun (k: (a,_) continuation) -> 
      match !internal with
      | tok :: buf ->
        internal := buf;
        continue k tok
      | [] -> Reporter.fatalf Parse_error "EOF"
      )
    | Shift pos -> Some (fun k -> internal := pos; continue k ())
    | CurrentPosition -> Some (fun k -> continue k !internal)
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

let rec many (p : unit -> 'a) : 'a list =
  let pos = current_position () in
  try
    let x = p () in
    x :: many p
  with | _ -> shift pos; []
let (<|>) (p1 : unit -> 'a) (p2 : unit -> 'a) () : 'a =
  let pos = current_position () in
  let x = (try p1 () with | _ ->
    shift pos; p2 ()) in
  x
