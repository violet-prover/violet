type t =
  { all : Reporter.Message.t Asai.Diagnostic.t Dynarray.t
  ; mutable has_errors : bool
  }

let create () = { all = Dynarray.create (); has_errors = false }

let is_error (d : _ Asai.Diagnostic.t) =
  match d.severity with
  | Error | Bug -> true
  | Hint | Info | Warning -> false
;;

let emit t (d : Reporter.Message.t Asai.Diagnostic.t) =
  Dynarray.add_last t.all d;
  if is_error d then t.has_errors <- true
;;

let all t = Dynarray.to_list t.all
let errors t = List.filter is_error (all t)
let has_errors t = t.has_errors
let latest_error t = Seq.find is_error (Dynarray.to_seq_rev t.all)
