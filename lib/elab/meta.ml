open Violet_kernel.Syntax.Core
open Bwd
open Bwd.Infix

let meta_context : (metavar, value) Hashtbl.t = Hashtbl.create ~random:true 100
let lookup_meta (mvar : metavar) : value option = Hashtbl.find_opt meta_context mvar

let insert_meta (mvar : metavar) (solution : value) : unit =
  Hashtbl.add meta_context mvar solution
;;

let eval (mvar : metavar) : value =
  match lookup_meta mvar with
  | Some t -> t
  | None -> Flex (mvar, Emp)
;;

let count = ref 0

(* Used by elaborator (Checker): fresh meta as a core term, applied to all
   currently-bound locals 0..lvl-1.  Eval of `InsertedMeta (m, lvl)` later will
   reconstruct the spine from the live env. *)
let meta_fresh (lvl : int) : term =
  let r = InsertedMeta (MetaVar !count, lvl) in
  incr count;
  r
;;

(* Used by Unification when inserting an implicit-Pi meta during unify: skips
   the term layer and synthesizes the `Flex (m, [$0;..;$lvl-1])` value
   directly, since unify operates on values and tracks lvl explicitly. *)
let fresh_meta_value (lvl : int) : value =
  let m = MetaVar !count in
  incr count;
  let rec build i acc =
    if i = lvl then acc else build (i + 1) (acc <: RigidLocal (i, Emp))
  in
  Flex (m, build 0 Emp)
;;

module View : Violet_kernel.Views.META_VIEW = struct
  let lookup = lookup_meta
  let eval = eval
end
