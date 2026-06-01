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

(* A fresh metavar with no spine/level attached. Used by pruning. *)
let fresh_metavar () : metavar =
  let m = MetaVar !count in
  incr count;
  m
;;

(* Metas that stand in for a user-placed `?` goal.  They are intentionally
   unsolved: the kernel's well-formedness check (`Check.check_term`) treats
   them as known, so a declaration containing goals still flows through
   `Module.declare` and remains usable by later definitions. *)
let goal_metas : (metavar, unit) Hashtbl.t = Hashtbl.create 32
let register_goal (mvar : metavar) : unit = Hashtbl.replace goal_metas mvar ()
let is_goal (mvar : metavar) : bool = Hashtbl.mem goal_metas mvar

(* Records where is an inserted meta came from, so `OrphanMeta` can be
   re-reported as `cannot infer implicit {x : X} at <loc>` instead of a
   raw `OrphanMeta ?34`. *)
type origin =
  { loc : Asai.Range.t
  ; display : string
  }

let origins : (metavar, origin) Hashtbl.t = Hashtbl.create 32
let register_origin (mvar : metavar) (o : origin) : unit = Hashtbl.replace origins mvar o
let origin_of (mvar : metavar) : origin option = Hashtbl.find_opt origins mvar

(* Fresh meta as a core term, applied to all currently-bound locals 0..lvl-1.
   Eval of `InsertedMeta (m, lvl)` later reconstructs the spine from the live
   env. *)
let meta_fresh (lvl : int) : term =
  let r = InsertedMeta (MetaVar !count, lvl) in
  incr count;
  r
;;

let meta_fresh_with (lvl : int) ~(origin : origin) : term =
  let mvar = MetaVar !count in
  register_origin mvar origin;
  incr count;
  InsertedMeta (mvar, lvl)
;;

let fresh_goal (lvl : int) : term =
  let mvar = MetaVar !count in
  incr count;
  register_goal mvar;
  InsertedMeta (mvar, lvl)
;;

(* Used by Unification when inserting an implicit-Pi meta during unify: skips
   the term layer and synthesizes the `Flex (m, [$0;..;$lvl-1])` value
   directly, since unify operates on values and tracks lvl explicitly. *)
let fresh_meta_value (lvl : int) : value =
  let m = MetaVar !count in
  incr count;
  let rec build i acc =
    if i = lvl then acc else build (i + 1) (acc <: explicit_arg (RigidLocal (i, Emp)))
  in
  Flex (m, build 0 Emp)
;;

let fresh_meta_value_with (lvl : int) ~(origin : origin) : value =
  let m = MetaVar !count in
  register_origin m origin;
  incr count;
  let rec build i acc =
    if i = lvl then acc else build (i + 1) (acc <: explicit_arg (RigidLocal (i, Emp)))
  in
  Flex (m, build 0 Emp)
;;

module View : Violet_kernel.Views.META_VIEW = struct
  let lookup = lookup_meta
  let eval = eval
  let is_goal = is_goal
end
