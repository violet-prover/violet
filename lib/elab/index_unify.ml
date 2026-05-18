(* First-order syntactic unification on Core values, used by `\elim`
   elaboration to compare a constructor's index spine against the target's
   index spine. *)

module Syntax = Violet_kernel.Syntax
module Level = Violet_kernel.Level
module Evaluation = Wiring.Eval
open Syntax
open Bwd
open Bwd.Infix

(* A flex variable is a local (RigidLocal at a specific de Bruijn LEVEL) that
   the unifier may solve. Any RigidLocal whose level isn't in this set, or any
   Var/Elim/etc., is rigid. *)
type flex_set = int list

let is_flex (flex : flex_set) (lvl : int) : bool = List.mem lvl flex

(* Substitution: maps a flex level to the term it was bound to. *)
type subst = (int * Core.value) list

type outcome =
  | Success of subst
  | Conflict of
      { position : int
      ; lhs : Core.value
      ; rhs : Core.value
      }
  | Stuck of
      { position : int
      ; lhs : Core.value
      ; rhs : Core.value
      }

(* Apply the accumulated substitution under whnf: if the head is a flex local
   whose level we've already solved, splice the bound value in (and re-force).
   Anything else stays. *)
let rec resolve (subst : subst) (v : Core.value) : Core.value =
  match Evaluation.force_head v with
  | Core.RigidLocal (lvl, sp) as v0 ->
    (match List.assoc_opt lvl subst with
     | Some bound -> resolve subst (Evaluation.vapp_spine bound sp)
     | None -> v0)
  | v0 -> v0
;;

(* Occurs check: does `lvl` appear anywhere in `v` after resolving through
   the current substitution? Conservative — returns true on unknown shapes
   (which only happens on neutrals that don't bottom out to a RigidLocal
   spine or a Label/IndType spine, so a true here just means we stay Stuck
   instead of binding). *)
let occurs (subst : subst) (lvl : int) (v : Core.value) : bool =
  let rec go v =
    match resolve subst v with
    | Core.RigidLocal (l, sp) -> l = lvl || Bwd.exists go sp
    | Core.Label (_, sp) -> Bwd.exists go sp
    | Core.IndType (_, sp) -> Bwd.exists go sp
    | Core.Var (_, sp) -> Bwd.exists go sp
    | Core.Elim (_, sp) -> Bwd.exists go sp
    | Core.Flex (_, sp) -> Bwd.exists go sp
    | Core.Universe _ -> false
    | _ -> true
  in
  go v
;;

let rec unify_one
          ~(flex : flex_set)
          ~(subst : subst)
          (position : int)
          (l : Core.value)
          (r : Core.value)
  : outcome
  =
  let l_orig = l in
  let r_orig = r in
  let l = resolve subst l in
  let r = resolve subst r in
  match l, r with
  | Core.RigidLocal (a, Emp), Core.RigidLocal (b, Emp) when a = b -> Success subst
  | Core.RigidLocal (lvl, Emp), other when is_flex flex lvl ->
    if occurs subst lvl other
    then Stuck { position; lhs = l_orig; rhs = r_orig }
    else Success ((lvl, other) :: subst)
  | other, Core.RigidLocal (lvl, Emp) when is_flex flex lvl ->
    if occurs subst lvl other
    then Stuck { position; lhs = l_orig; rhs = r_orig }
    else Success ((lvl, other) :: subst)
  (* Matching ctor heads: recurse pointwise. Inner head-mismatches
     (e.g. `suc zero` vs `suc (suc n)`) get demoted to Stuck — the
     downstream no-confusion machinery only discharges top-level conflicts
     at an index spine position; nested conflicts need injectivity. *)
  | Core.Label (n1, sp1), Core.Label (n2, sp2) when String.equal n1 n2 ->
    unify_spines_inner
      ~flex
      ~subst
      position
      (Bwd.to_list sp1)
      (Bwd.to_list sp2)
      ~outer_l:l_orig
      ~outer_r:r_orig
  (* Distinct ctor heads: orthogonal, case is unreachable. *)
  | Core.Label (_, _), Core.Label (_, _) ->
    Conflict { position; lhs = l_orig; rhs = r_orig }
  | Core.IndType (n1, sp1), Core.IndType (n2, sp2) when String.equal n1 n2 ->
    unify_spines_inner
      ~flex
      ~subst
      position
      (Bwd.to_list sp1)
      (Bwd.to_list sp2)
      ~outer_l:l_orig
      ~outer_r:r_orig
  | Core.Universe l1, Core.Universe l2 when Level.equal l1 l2 -> Success subst
  | _ -> Stuck { position; lhs = l_orig; rhs = r_orig }

(* Spine recursion for matching heads: any nested Conflict becomes Stuck on
   the outer values. Success and Stuck propagate as usual. *)
and unify_spines_inner
      ~(flex : flex_set)
      ~(subst : subst)
      (position : int)
      (ls : Core.value list)
      (rs : Core.value list)
      ~(outer_l : Core.value)
      ~(outer_r : Core.value)
  : outcome
  =
  match ls, rs with
  | [], [] -> Success subst
  | x :: xs, y :: ys ->
    (match unify_one ~flex ~subst position x y with
     | Conflict _ -> Stuck { position; lhs = outer_l; rhs = outer_r }
     | Stuck _ as s -> s
     | Success subst' ->
       unify_spines_inner ~flex ~subst:subst' position xs ys ~outer_l ~outer_r)
  | _ -> Stuck { position; lhs = outer_l; rhs = outer_r }
;;

(* Walk index spines position by position. Outcome precedence:
   any Conflict wins (case is unreachable regardless of other positions); else
   any Stuck propagates with its earliest occurrence; else all Successes
   compose into a single substitution. *)
let unify ~(flex : flex_set) ~(lhs : Core.value list) ~(rhs : Core.value list) : outcome =
  if List.length lhs <> List.length rhs
  then
    Stuck
      { position = 0; lhs = Core.Universe Level.LZero; rhs = Core.Universe Level.LZero }
  else (
    let rec walk pos subst remembered_stuck = function
      | [], [] ->
        (match remembered_stuck with
         | Some s -> s
         | None -> Success subst)
      | l :: ls, r :: rs ->
        (match unify_one ~flex ~subst pos l r with
         | Conflict _ as c -> c
         | Stuck _ as s ->
           let remembered =
             match remembered_stuck with
             | Some _ -> remembered_stuck
             | None -> Some s
           in
           walk (pos + 1) subst remembered (ls, rs)
         | Success subst' -> walk (pos + 1) subst' remembered_stuck (ls, rs))
      | _ ->
        Stuck
          { position = pos
          ; lhs = Core.Universe Level.LZero
          ; rhs = Core.Universe Level.LZero
          }
    in
    walk 0 [] None (lhs, rhs))
;;

(* Inline tests. We hand-build values rather than going through elaboration
   so the tests don't depend on the kernel's meta/env state. *)

let%expect_test "unify: same rigid local — Success []" =
  let v = Core.RigidLocal (3, Emp) in
  let o = unify ~flex:[] ~lhs:[ v ] ~rhs:[ v ] in
  (match o with
   | Success s -> Printf.printf "Success len=%d" (List.length s)
   | Conflict _ -> print_string "Conflict"
   | Stuck _ -> print_string "Stuck");
  [%expect {| Success len=0 |}]
;;

let%expect_test "unify: distinct rigid locals — Stuck" =
  let a = Core.RigidLocal (3, Emp) in
  let b = Core.RigidLocal (4, Emp) in
  let o = unify ~flex:[] ~lhs:[ a ] ~rhs:[ b ] in
  (match o with
   | Success _ -> print_string "Success"
   | Conflict _ -> print_string "Conflict"
   | Stuck _ -> print_string "Stuck");
  [%expect {| Stuck |}]
;;

let%expect_test "unify: flex var binds to rigid local" =
  let flex_lvl = 7 in
  let m = Core.RigidLocal (flex_lvl, Emp) in
  let n = Core.RigidLocal (3, Emp) in
  let o = unify ~flex:[ flex_lvl ] ~lhs:[ m ] ~rhs:[ n ] in
  (match o with
   | Success s ->
     Printf.printf
       "Success [%s]"
       (String.concat "," (List.map (fun (l, _) -> string_of_int l) s))
   | Conflict _ -> print_string "Conflict"
   | Stuck _ -> print_string "Stuck");
  [%expect {| Success [7] |}]
;;

let%expect_test "unify: same ctor head with single arg — recurses" =
  let a = Core.Label ("suc", Emp <: Core.RigidLocal (1, Emp)) in
  let b = Core.Label ("suc", Emp <: Core.RigidLocal (1, Emp)) in
  let o = unify ~flex:[] ~lhs:[ a ] ~rhs:[ b ] in
  (match o with
   | Success s -> Printf.printf "Success len=%d" (List.length s)
   | Conflict _ -> print_string "Conflict"
   | Stuck _ -> print_string "Stuck");
  [%expect {| Success len=0 |}]
;;

let%expect_test "unify: different ctor heads — Conflict" =
  let a = Core.Label ("zero", Emp) in
  let b = Core.Label ("suc", Emp <: Core.RigidLocal (1, Emp)) in
  let o = unify ~flex:[] ~lhs:[ a ] ~rhs:[ b ] in
  (match o with
   | Success _ -> print_string "Success"
   | Conflict c -> Printf.printf "Conflict at %d" c.position
   | Stuck _ -> print_string "Stuck");
  [%expect {| Conflict at 0 |}]
;;

let%expect_test "unify: flex inside ctor — recurses and binds" =
  let flex_lvl = 9 in
  let lhs = Core.Label ("suc", Emp <: Core.RigidLocal (flex_lvl, Emp)) in
  let rhs = Core.Label ("suc", Emp <: Core.RigidLocal (3, Emp)) in
  let o = unify ~flex:[ flex_lvl ] ~lhs:[ lhs ] ~rhs:[ rhs ] in
  (match o with
   | Success s ->
     Printf.printf
       "Success bound=%d"
       (match List.assoc_opt flex_lvl s with
        | Some (Core.RigidLocal (l, _)) -> l
        | _ -> -1)
   | Conflict _ -> print_string "Conflict"
   | Stuck _ -> print_string "Stuck");
  [%expect {| Success bound=3 |}]
;;

let%expect_test "unify: Conflict precedence over Stuck across positions" =
  (* Position 0: stuck (two distinct rigid locals).
     Position 1: conflict (zero vs suc).
     Walk should report Conflict at position 1. *)
  let lhs = [ Core.RigidLocal (1, Emp); Core.Label ("zero", Emp) ] in
  let rhs =
    [ Core.RigidLocal (2, Emp); Core.Label ("suc", Emp <: Core.RigidLocal (5, Emp)) ]
  in
  let o = unify ~flex:[] ~lhs ~rhs in
  (match o with
   | Success _ -> print_string "Success"
   | Conflict c -> Printf.printf "Conflict at %d" c.position
   | Stuck s -> Printf.printf "Stuck at %d" s.position);
  [%expect {| Conflict at 1 |}]
;;

let%expect_test "unify: Stuck wins over Success when present" =
  (* Position 0: stuck. Position 1: success. Overall: Stuck. *)
  let lhs = [ Core.RigidLocal (1, Emp); Core.RigidLocal (5, Emp) ] in
  let rhs = [ Core.RigidLocal (2, Emp); Core.RigidLocal (5, Emp) ] in
  let o = unify ~flex:[] ~lhs ~rhs in
  (match o with
   | Success _ -> print_string "Success"
   | Conflict _ -> print_string "Conflict"
   | Stuck s -> Printf.printf "Stuck at %d" s.position);
  [%expect {| Stuck at 0 |}]
;;

let%expect_test "unify: composed subst — m := n binds once, propagates" =
  (* lhs = [ m, suc m ]; rhs = [ n, suc n ]; flex m. *)
  let flex_lvl = 9 in
  let m = Core.RigidLocal (flex_lvl, Emp) in
  let n = Core.RigidLocal (3, Emp) in
  let lhs = [ m; Core.Label ("suc", Emp <: m) ] in
  let rhs = [ n; Core.Label ("suc", Emp <: n) ] in
  let o = unify ~flex:[ flex_lvl ] ~lhs ~rhs in
  (match o with
   | Success s ->
     Printf.printf
       "Success bound=%d"
       (match List.assoc_opt flex_lvl s with
        | Some (Core.RigidLocal (l, _)) -> l
        | _ -> -1)
   | Conflict _ -> print_string "Conflict"
   | Stuck _ -> print_string "Stuck");
  [%expect {| Success bound=3 |}]
;;

let%expect_test "unify: occurs check — m := suc m fails Stuck" =
  let flex_lvl = 11 in
  let m = Core.RigidLocal (flex_lvl, Emp) in
  let suc_m = Core.Label ("suc", Emp <: m) in
  let o = unify ~flex:[ flex_lvl ] ~lhs:[ m ] ~rhs:[ suc_m ] in
  (match o with
   | Success _ -> print_string "Success"
   | Conflict _ -> print_string "Conflict"
   | Stuck _ -> print_string "Stuck");
  [%expect {| Stuck |}]
;;
