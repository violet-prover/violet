open Syntax
open Bwd
open Evaluation

module Bound = struct
  type t = string bwd
end
module BoundState = Algaeff.State.Make (Bound)

let rec unify (a : Core.value) (b : Core.value) : unit =
  Eio.traceln "%s ?= %s" ([%show: Core.value] a) ([%show: Core.value] b);
  match (force a, force b) with
  | Universe, Universe -> ()
  | Rigid (h1, sp1), Rigid (h2, sp2) when String.equal h1 h2 ->
      unify_spine sp1 sp2
  | Flex (m1, sp1), Flex (m2, sp2) when m1 = m2 -> unify_spine sp1 sp2
  | t, Flex (m, sp) | Flex (m, sp), t -> Meta.solve m sp t
  | expected, actual ->
      Reporter.fatalf Type_error "cannot unify `%s` and `%s`"
        ([%show: Core.value] expected)
        ([%show: Core.value] actual)

and unify_spine (xs : Core.value bwd) (ys : Core.value bwd) : unit =
  match (xs, ys) with
  | Emp, Emp -> ()
  | Snoc (xs, x), Snoc (ys, y) ->
      unify_spine xs ys;
      unify x y
  | _, _ -> Reporter.fatalf Elab_error "cannot unify, spine mismatched"

let rec check (term : Surface.preterm) (typ : Core.value_ty) : Core.term =
  match (term, typ) with
  | ( Lambda { name = x; bound = body; implicit = lambda_mode },
      VPi ({ name = _; bound = a; implicit = pi_mode }, b) ) ->
      if lambda_mode != pi_mode then
        Reporter.fatalf Elab_error "mode mismatching"
      else
        Context.S.section [] @@ fun () ->
        Context.S.import_singleton ([ x ], (a, `Local));
        let body = check body (b (Rigid (x, Emp))) in
        Core.Lambda { name = x; bound = body; implicit = lambda_mode }
  | Hole, _ -> Meta.fresh (BoundState.get ())
  | tm, expected_typ ->
      let tm, infer_typ = infer tm in
      unify expected_typ infer_typ;
      tm

(* infer 的用途是，把已經裝飾過的 surface term 變成 core term，並且推導其型別，這個過程可以失敗 *)
and infer : Surface.preterm -> Core.term * Core.value_ty = function
  | Located { loc; value } -> Reporter.with_loc loc @@ fun () -> infer value
  | Universe -> (Universe, Universe)
  | Var x -> (Var x, Context.lookup x)
  | Pi ({ name; bound = a; implicit }, b) ->
      let a = check a Universe in
      (* 引入一層 x = x 的 environment *)
      Env.S.section [] @@ fun () ->
      Eio.traceln "applied %s" ([%show: Core.value] (Rigid (name, Bwd.Emp)));
      Env.S.include_singleton ([ name ], (Rigid (name, Bwd.Emp), `Local));
      (* 引入新的一層 context 並引入 name : A，檢查 B : U *)
      Context.S.section [] @@ fun () ->
      Context.S.include_singleton ([ name ], (eval a, `Local));
      let b = check b Universe in
      (Core.Pi ({ name; bound = a; implicit }, b), Core.Universe)
  | App (is_implicit, f, arg) -> (
      let f', f_typ = infer f in
      match f_typ with
      | VPi ({ implicit; name = _; bound = a }, b) ->
          if is_implicit == implicit then
            let arg' = check arg a in
            (App (f', arg'), b @@ eval arg')
          else if implicit then
            infer @@ App (false, App (implicit, f, Hole), arg)
          else
            Reporter.fatalf Elab_error "Bad apply %s %s"
              ([%show: Surface.preterm] f)
              ([%show: Surface.preterm] arg)
      | ty ->
          Reporter.fatalf Type_error
            "cannot apply a value to something with type `%s`"
            ([%show: Core.value_ty] ty))
  | Hole ->
      let ty = eval @@ Meta.fresh (BoundState.get ()) in
      let t = Meta.fresh (BoundState.get ()) in
      (t, ty)
  | Lambda _ -> Reporter.fatalf Elab_error "cannot infer lambda term"

let check_module (file : Surface.t) : unit =
  BoundState.run ~init:Emp @@ fun () ->
  List.iter
    (fun top ->
      match top with
      | Surface.Let (name, bindings, result_ty, body) ->
BoundState.set @@ Bwd.of_list (List.map (fun b -> b.name) bindings);
          let typ : Surface.pretype =
            List.fold_right
              (fun binding return_ty -> Surface.Pi (binding, return_ty))
              bindings result_ty
          in
          Eio.traceln "top let %s : %s" name ([%show: Surface.pretype] typ);
          let typ = Context.S.section [] @@ fun () -> check typ Universe in
          let typ = Env.S.section [] @@ fun () -> eval typ in

          let term : Surface.preterm =
            List.fold_right
              (fun { name; implicit; bound = _ } body ->
                Surface.Lambda { name; bound = body; implicit })
              bindings body
          in
          Eio.traceln "top let %s = %s" name ([%show: Surface.pretype] term);
          let term = Context.S.section [] @@ fun () -> check term typ in

          Context.S.include_singleton ~context_visible:`Visible
            ~context_export:`Export
            ([ name ], (typ, `Local));

          Env.S.include_singleton ~context_visible:`Visible
            ~context_export:`Export
            ([ name ], (Env.S.section [] @@ fun () -> eval term, `Local));

          ())
    file.tops
