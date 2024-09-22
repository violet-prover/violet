open Syntax
open Bwd
open Evaluation

let count = ref 0

let fresh_variable () : Core.value =
  let r = Format.sprintf "*%d" !count in
  count := !count + 1;
  Rigid (r, Emp)

let rec unify ~loc (a : Core.value) (b : Core.value) : unit =
  match (force a, force b) with
  | Universe, Universe -> ()
  | Rigid (h1, sp1), Rigid (h2, sp2) when String.equal h1 h2 ->
      unify_spine ~loc sp1 sp2
  | VLambda { bound = bound1; _ }, VLambda { bound = bound2; _ } ->
      let x = fresh_variable () in
      unify ~loc (bound1 x) (bound2 x)
  | VLambda { bound; _ }, t | t, VLambda { bound; _ } ->
      let x = fresh_variable () in
      unify ~loc (bound x) (vapp t x)
  | VPi (_, b1), VPi (_, b2) ->
      let x = fresh_variable () in
      unify ~loc (b1 x) (b2 x)
  | Flex (m1, sp1), Flex (m2, sp2) when m1 = m2 -> unify_spine ~loc sp1 sp2
  | t, Flex (m, sp) | Flex (m, sp), t -> Meta.solve m sp t
  | expected, actual ->
      Reporter.fatalf ~loc Type_error
        "cannot unify `%s ?= %s` (or verbose `%s ?= %s`)"
        ([%show: Core.value] expected)
        ([%show: Core.value] actual)
        ([%show: Core.value] a)
        ([%show: Core.value] b)

and unify_spine ~loc (xs : Core.value bwd) (ys : Core.value bwd) : unit =
  match (xs, ys) with
  | Emp, Emp -> ()
  | Snoc (xs, x), Snoc (ys, y) ->
      unify_spine ~loc xs ys;
      unify ~loc x y
  | _, _ -> Reporter.fatalf ~loc Elab_error "cannot unify, spine mismatched"
