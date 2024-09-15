open Effect
open Effect.Deep

type _ Effect.t += Next : Lexer.token Asai.Range.located Effect.t
                 | Shift : Lexer.token Asai.Range.located list -> unit Effect.t
                 | CurrentPosition :  Lexer.token Asai.Range.located list Effect.t

let next_token ()  = perform Next
let shift pos = perform (Shift pos)
let current_position () = perform CurrentPosition

let run (buf : Lexer.token Asai.Range.located list) (f : unit -> 'a) : 'a = 
  let internal  = ref buf in
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
  List.rev !res
let (<|>) (p1 : unit -> 'a) (p2 : unit -> 'a) () : 'a =
  let pos = current_position () in
  let x = (try p1 () with | _ ->
    shift pos; p2 ()) in
  x
