open Syntax

exception TODO

let rec eval (tm : Core.term) : Core.value =
  match tm with
  | Universe -> Universe
  | Var x -> Env.lookup x
  | Pi ({name;bound;implicit}, b) ->
    Core.VPi (
      {name;bound=eval bound;implicit},
      fun v ->
        Env.S.section [] @@ fun () ->
        Env.S.include_singleton ([name], (v, `Local));
        eval b
    )
  | Lambda ({name;bound;implicit=_}) ->
    VLambda (fun v ->
      Env.S.section [] @@ fun () ->
      Env.S.include_singleton ([name], (v, `Local));
      eval bound)
  | Meta _ -> raise TODO
  | InsertedMeta _ -> raise TODO

let unify (a : Core.value) (b : Core.value) : unit =
  match a, b with
  | Universe, Universe -> ()
  | expected, actual ->
    Reporter.fatalf Type_error
      "cannot unify `%s` and `%s`"
      ([%show: Core.value] expected)
      ([%show: Core.value] actual)

let rec check (term : Surface.preterm) (typ : Core.value_ty) : Core.term =
  match term, typ with
  | Lambda {name=x; bound=body; implicit=lambda_mode}, VPi ({name=_; bound=a; implicit=pi_mode}, b) ->
    if lambda_mode != pi_mode then
      Reporter.fatalf Elab_error "mode mismatching" 
    else
      Context.S.section [] @@ fun () ->
      Context.S.import_singleton ( [x], (a, `Local));
      let body = check body (b a) in
      Core.Lambda {name=x; bound=body; implicit=lambda_mode}
  | tm, expected_typ ->
    let tm, infer_typ = infer tm in
    unify expected_typ infer_typ;
    tm
and infer : Surface.preterm -> Core.term * Core.value_ty = function
  | Located {loc; value} ->
    Reporter.merge_loc loc @@ fun () ->
    infer value
  | Universe -> (Universe, Universe)
  | Var x -> (Var x, Context.lookup x)
  | Pi ({name; bound=a; implicit}, b) ->
    let a = check a Universe in
    (* 引入一層 x = x 的 environment *)
    Env.S.section [] @@ fun () ->
    Env.S.include_singleton ([name], (Rigid (name, Bwd.Emp), `Local));
    (* 引入新的一層 context 並引入 name : A，檢查 B : U *)
    Context.S.section [] @@ fun () ->
    Context.S.include_singleton ( [name], (eval a, `Local));
    let b = check b Universe in
    (Core.Pi ({name; bound=a; implicit}, b), Core.Universe)
  | _ -> raise TODO

let check_module (file : Surface.t) : unit =
  List.iter (fun top ->
    match top with
    | Surface.Let (name, bindings, result_ty, body) ->
      let typ : Surface.pretype = List.fold_right (fun binding return_ty ->
        Surface.Pi (binding, return_ty))
        bindings
        result_ty in
      Eio.traceln "%s" ([%show: Surface.pretype] typ);
      let typ = check typ Universe in
      let typ = eval typ in

      let term : Surface.preterm = List.fold_right
        (fun {name;implicit;bound=_} body -> Surface.Lambda {name; bound=body; implicit})
        bindings
        body in
      Eio.traceln "%s" ([%show: Surface.pretype] term);
      let term = check term typ in

      Context.S.include_singleton ~context_visible:`Visible
        ~context_export:`Export
        ([ name ], (typ, `Local));

      Env.S.include_singleton ~context_visible:`Visible
        ~context_export:`Export
        ([name], (eval term, `Local));

      ()
    )
  file.tops
