open Syntax
open Bwd
open Bwd.Infix

exception TODO

let vapp (t : Core.value) (u : Core.value) : Core.value =
  match t with
  | VLambda f -> f u
  | Flex (m, t) -> Flex (m, t <: u)
  | Rigid (h, t) -> Rigid (h, t <: u)
  | v -> Reporter.fatalf Elab_error "cannot apply on %s" ([%show: Core.value] v)

let rec eval (tm : Core.term) : Core.value =
  match tm with
  | Universe -> Universe
  | Var x -> Env.lookup x
  | App (t, u) ->
      let t = eval t in
      let u = eval u in
      vapp t u
  | Pi ({ name; bound; implicit }, b) ->
      Core.VPi
        ( { name; bound = eval bound; implicit },
          fun v ->
            Env.S.section [] @@ fun () ->
            Env.S.include_singleton ([ name ], (v, `Local));
            eval b )
  | Lambda { name; bound; implicit = _ } ->
      VLambda
        (fun v ->
          Env.S.section [] @@ fun () ->
          Env.S.include_singleton ([ name ], (v, `Local));
          eval bound)
  | Meta m -> Meta.eval m
  | InsertedMeta _ -> raise TODO

let unify (a : Core.value) (b : Core.value) : unit =
  match (a, b) with
  | Universe, Universe -> ()
  (* FIXME: should invoke solver here to update our cute meta context *)
  | t, Flex (m, sp)
  | Flex (m, sp), t ->
    Meta.solve m sp t
  | expected, actual ->
      Reporter.fatalf Type_error "cannot unify `%s` and `%s`"
        ([%show: Core.value] expected)
        ([%show: Core.value] actual)

let rec check (term : Surface.preterm) (typ : Core.value_ty) : Core.term =
  match (term, typ) with
  | ( Lambda { name = x; bound = body; implicit = lambda_mode },
      VPi ({ name = _; bound = a; implicit = pi_mode }, b) ) ->
      if lambda_mode != pi_mode then
        Reporter.fatalf Elab_error "mode mismatching"
      else
        Context.S.section [] @@ fun () ->
        Context.S.import_singleton ([ x ], (a, `Local));
        let body = check body (b a) in
        Core.Lambda { name = x; bound = body; implicit = lambda_mode }
  | Hole, _ ->
      Meta.fresh ()
  | tm, expected_typ ->
      let tm, infer_typ = infer tm in
      unify expected_typ infer_typ;
      tm

(* infer 的用途是，把已經裝飾過的 surface term 變成 core term，並且推導其型別，這個過程可以失敗 *)
and infer : Surface.preterm -> Core.term * Core.value_ty = function
  | Located { loc; value } -> Reporter.merge_loc loc @@ fun () -> infer value
  | Universe -> (Universe, Universe)
  | Var x -> (Var x, Context.lookup x)
  | Pi ({ name; bound = a; implicit }, b) ->
      let a = check a Universe in
      (* 引入一層 x = x 的 environment *)
      Env.S.section [] @@ fun () ->
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
            infer @@ App (false, (App (implicit, f, Hole)), arg)
          else
            Reporter.fatalf Elab_error "Bad apply %s %s"
              ([%show: Surface.preterm] f)
              ([%show: Surface.preterm] arg)
      | ty ->
          Reporter.fatalf Type_error
            "cannot apply a value to something with type `%s`"
            ([%show: Core.value_ty] ty))
  | Hole ->
    let ty = eval @@ Meta.fresh () in
    let t = Meta.fresh () in
    (t, ty)
  | _ -> raise TODO

let check_module (file : Surface.t) : unit =
  List.iter
    (fun top ->
      match top with
      | Surface.Let (name, bindings, result_ty, body) ->
          let typ : Surface.pretype =
            List.fold_right
              (fun binding return_ty -> Surface.Pi (binding, return_ty))
              bindings result_ty
          in
          Eio.traceln "%s" ([%show: Surface.pretype] typ);
          let typ = check typ Universe in
          let typ = eval typ in

          let term : Surface.preterm =
            List.fold_right
              (fun { name; implicit; bound = _ } body ->
                Surface.Lambda { name; bound = body; implicit })
              bindings body
          in
          Eio.traceln "%s" ([%show: Surface.pretype] term);
          let term = check term typ in

          Context.S.include_singleton ~context_visible:`Visible
            ~context_export:`Export
            ([ name ], (typ, `Local));

          Env.S.include_singleton ~context_visible:`Visible
            ~context_export:`Export
            ([ name ], (eval term, `Local));

          ())
    file.tops
