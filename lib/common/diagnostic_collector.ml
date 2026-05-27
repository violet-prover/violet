type t =
  { mutable rev_all : Reporter.Message.t Asai.Diagnostic.t list
  ; mutable has_errors : bool
  }

let create () = { rev_all = []; has_errors = false }

let is_error (d : _ Asai.Diagnostic.t) =
  match d.severity with
  | Error | Bug -> true
  | Hint | Info | Warning -> false
;;

let emit t (d : Reporter.Message.t Asai.Diagnostic.t) =
  t.rev_all <- d :: t.rev_all;
  if is_error d then t.has_errors <- true
;;

let all t = List.rev t.rev_all
let errors t = List.rev (List.filter is_error t.rev_all)
let has_errors t = t.has_errors
let latest_error t = List.find_opt is_error t.rev_all
