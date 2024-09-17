exception Impossible

module Tokens = struct
  type t = Lexer.token Asai.Range.located list
end

module TokenState = Algaeff.State.Make (Tokens)

let next_token () =
  match TokenState.get () with
  | [ eof ] -> eof
  | tok :: buf ->
      TokenState.set buf;
      tok
  | [] -> raise Impossible

let shift pos = TokenState.set pos
let current_position () = TokenState.get ()

let run (init : Lexer.token Asai.Range.located list) (f : unit -> 'a) : 'a =
  TokenState.run ~init @@ fun () -> f ()

let consume (predict : Lexer.token) : unit =
  let tok = next_token () in
  if tok.value == predict then ()
  else
    let loc = Option.get tok.loc in
    Reporter.fatalf ~loc Parse_error "expected `%s`, but got `%s`"
      ([%show: Lexer.token] predict)
      ([%show: Lexer.token] tok.value)

let rec many (p : unit -> 'a) () : 'a list =
  let pos = current_position () in
  let x = Reporter.try_with
    ~fatal:(fun d ->
      match d.message with
      | Parse_error -> shift pos; None
      | _ -> Reporter.fatal_diagnostic d)
    (fun () -> Some (p ()))
  in
  match x with
  | None -> []
  | Some x -> x :: many p ()

let ( <|> ) (p1 : unit -> 'a) (p2 : unit -> 'a) () : 'a =
  let pos = current_position () in
  try p1 ()
  with _ ->
    shift pos;
    p2 ()
