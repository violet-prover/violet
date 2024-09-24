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

let current_loc () : Asai.Range.t option =
  let pos = current_position () in
  let tok = next_token () in
  shift pos;
  tok.loc

let consume (predict : Lexer.token) : unit =
  let tok = next_token () in
  if tok.value == predict then ()
  else
    let loc = Option.get tok.loc in
    Reporter.fatalf ~loc Parse_error "expected `%s`, but got `%s`"
      ([%show: Lexer.token] predict)
      ([%show: Lexer.token] tok.value)

let catch_parse_error (p : unit -> 'a) : 'a option =
  let pos = current_position () in
  Reporter.try_with
    ~fatal:(fun d ->
      match d.message with
      | Parse_error ->
          shift pos;
          None
      | _ -> Reporter.fatal_diagnostic d)
    (fun () -> Some (p ()))

let rec many (p : unit -> 'a) () : 'a list =
  let x = catch_parse_error p in
  match x with None -> [] | Some x -> x :: many p ()

let ( <|> ) (p1 : unit -> 'a) (p2 : unit -> 'a) () : 'a =
  match catch_parse_error p1 with None -> p2 () | Some x -> x

let rec infix (op : unit -> 'a -> 'a -> 'a) (tm : unit -> 'a) () : 'a =
  let lhs = tm () in
  match catch_parse_error op with
  | Some bin ->
      let rhs = infix op tm () in
      bin lhs rhs
  | None -> lhs
