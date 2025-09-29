open Syntax
open Bwd
open Evaluation

let rec check ~loc (term : Surface.preterm) (typ : Core.value_ty) : Core.term =
  match term, typ with
  | ( Lambda { name = x; bound = body; implicit = lambda_mode }
    , VPi ({ name = _; bound = a; implicit = pi_mode }, b) ) ->
    if lambda_mode != pi_mode
    then Reporter.fatalf ~loc Elab_error "mode mismatching"
    else
      Context.S.section []
      @@ fun () ->
      Context.S.import_singleton ([ x ], (a, `Local));
      let body = check ~loc body (b (Rigid (x, Emp))) in
      Core.Lambda { name = x; bound = body; implicit = lambda_mode }
  | Hole, _ -> Meta.meta_fresh ()
  | tm, expected_typ ->
    let tm, infer_typ = infer ~loc tm in
    Unification.unify ~loc expected_typ infer_typ;
    tm

(* infer 的用途是，把已經裝飾過的 surface term 變成 core term，並且推導其型別，這個過程可以失敗 *)
and infer ~loc : Surface.preterm -> Core.term * Core.value_ty = function
  | Located { loc; value } -> infer ~loc:(Option.get loc) value
  | Universe -> Universe, Universe
  | Var x -> Var x, Context.lookup x
  | Pi ({ name; bound = a; implicit }, b) ->
    let a = check ~loc a Universe in
    (* 引入一層 x = x 的 environment *)
    Env.S.section []
    @@ fun () ->
    Env.S.include_singleton ([ name ], (Rigid (name, Bwd.Emp), `Local));
    (* 引入新的一層 context 並引入 name : A，檢查 B : U *)
    Context.S.section []
    @@ fun () ->
    Context.S.include_singleton ([ name ], (eval a, `Local));
    let b = check ~loc b Universe in
    Core.Pi ({ name; bound = a; implicit }, b), Core.Universe
  | App (is_implicit, f, arg) ->
    let f', f_typ = infer ~loc f in
    (match f_typ with
     | VPi ({ implicit; name = _; bound = a }, b) ->
       if is_implicit == implicit
       then (
         let arg' = check ~loc arg a in
         App (f', arg'), b @@ eval arg')
       else if implicit
       then infer ~loc @@ App (false, App (implicit, f, Hole), arg)
       else
         Reporter.fatalf
           ~loc
           Elab_error
           "Bad apply %s %s"
           ([%show: Surface.preterm] f)
           ([%show: Surface.preterm] arg)
     | ty ->
       Reporter.fatalf
         ~loc
         Type_error
         "cannot apply a value to something with type `%s`"
         ([%show: Core.value_ty] ty))
  | Hole ->
    let ty = eval @@ Meta.meta_fresh () in
    let t = Meta.meta_fresh () in
    t, ty
  | Lambda _ -> Reporter.fatalf ~loc Elab_error "cannot infer lambda term"
;;

let bind_constructor ~loc params ({ name; bound; _ } : Surface.pretype binder) : unit =
  let typ : Surface.pretype =
    List.fold_right
      (fun { name; bound; _ } return_ty ->
         Surface.Pi ({ name; bound; implicit = true }, return_ty))
      params
      bound
  in
  let ctor_ty = check ~loc typ Universe in
  let ctor_ty = eval ctor_ty in
  Meta.GlobalState.set (Meta.GlobalDefs.add name @@ Meta.GlobalState.get ());
  Context.S.include_singleton ([ name ], (ctor_ty, `Local));
  Env.S.include_singleton ([ name ], (Rigid (name, Bwd.Emp), `Local))
;;

let rec check_module (file : Surface.t) : unit =
  let module_name = Filename.chop_extension @@ Filename.basename file.name in
  Eio.traceln "checking [module] %s (%s)" module_name file.name;
  Context.S.section [ module_name ]
  @@ fun () ->
  Env.S.section [ module_name ]
  @@ fun () ->
  Meta.BoundState.run ~init:Emp
  @@ fun () ->
  List.iter
    (fun (top : Surface.top Asai.Range.located) ->
       let loc = Option.get top.loc in
       check_top ~loc top.value)
    file.tops

and check_top ~loc top =
  match top with
  | Surface.Import library ->
    (* TODO: this hardcoded `example` shuold be removed in the future *)
    let filepath = "example/" ^ String.concat "/" library ^ ".vt" in
    let m = Parser.parse_file filepath in
    check_module m;
    (Context.S.modify_visible @@ Yuujinchou.Language.(union [ all; renaming library [] ]));
    Env.S.modify_visible @@ Yuujinchou.Language.(union [ all; renaming library [] ])
  | Surface.Data { name; params; ind_ty; clauses } ->
    Reporter.tracef ~loc "checking [inductive data type] %s" name
    @@ fun () ->
    let typ : Surface.pretype =
      List.fold_right
        (fun binding return_ty -> Surface.Pi (binding, return_ty))
        params
        ind_ty
    in
    let typ = check ~loc typ Universe in
    let typ = eval typ in
    Meta.GlobalState.set (Meta.GlobalDefs.add name @@ Meta.GlobalState.get ());
    Context.S.include_singleton
      ~context_visible:`Visible
      ~context_export:`Export
      ([ name ], (typ, `Local));
    Env.S.include_singleton
      ~context_visible:`Visible
      ~context_export:`Export
      ([ name ], (Rigid (name, Bwd.Emp), `Local));
    List.iter (bind_constructor ~loc params) clauses
  | Surface.Let (name, bindings, result_ty, body) ->
    Meta.BoundState.set @@ Bwd.of_list (List.map (fun b -> b.name) bindings);
    let typ : Surface.pretype =
      List.fold_right
        (fun binding return_ty -> Surface.Pi (binding, return_ty))
        bindings
        result_ty
    in
    Reporter.tracef ~loc "checking [top let] %s : %s" name ([%show: Surface.pretype] typ)
    @@ fun () ->
    let typ = check ~loc typ Universe in
    let typ = eval typ in
    let term : Surface.preterm =
      List.fold_right
        (fun { name; implicit; bound = _ } body ->
           Surface.Lambda { name; bound = body; implicit })
        bindings
        body
    in
    let term = check ~loc term typ in
    Context.S.include_singleton
      ~context_visible:`Visible
      ~context_export:`Export
      ([ name ], (typ, `Local));
    Env.S.include_singleton
      ~context_visible:`Visible
      ~context_export:`Export
      ([ name ], Env.S.section [] @@ fun () -> eval term, `Local);
    ()
;;
