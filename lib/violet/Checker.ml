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
    Eio.traceln
      "checking `%s` has type `%s ~ %s`\n"
      ([%show: Core.term] tm)
      ([%show: Core.value] expected_typ)
      ([%show: Core.value] infer_typ);
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
       then begin
         let arg' = check ~loc arg a in
         App (f', arg'), b @@ eval arg'
       end
       else if implicit
       then begin
         infer ~loc @@ App (false, App (implicit, f, Hole), arg)
       end
       else begin
         Reporter.fatalf
           ~loc
           Elab_error
           "Bad apply %s %s"
           ([%show: Surface.preterm] f)
           ([%show: Surface.preterm] arg)
       end
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
  | TypedLambda ({ name; bound = ty; implicit }, body) ->
    Env.S.section []
    @@ fun () ->
    Env.S.include_singleton ([ name ], (Rigid (name, Bwd.Emp), `Local));
    Context.S.section []
    @@ fun () ->
    let ty = check_type ~loc ty in
    Context.S.include_singleton ([ name ], (eval ty, `Local));
    let body, ty_of_body = infer ~loc body in
    ( Core.TypedLambda ({ name; bound = ty; implicit }, body)
    , Core.VPi ({ name; bound = eval ty; implicit }, fun _ -> ty_of_body) )
  | Lambda _ -> Reporter.fatalf ~loc Elab_error "cannot infer lambda term"

and check_type ~loc pretype : Core.term = check ~loc pretype Universe

let bind_constructor ~loc ({ name; bound = typ; _ } : Surface.pretype binder) : unit =
  let ctor_ty = check ~loc typ Universe in
  let ctor_ty = eval ctor_ty in
  Context.S.include_singleton ([ name ], (ctor_ty, `Local));
  Env.S.include_singleton ([ name ], (Label (name, Bwd.Emp), `Local))
;;

let bind_of_case
      ~loc
      ind_name
      motive_name
      ({ name; bound = typ; _ } : Surface.pretype binder)
  : Surface.pretype binder
  =
  let tele = Surface.telescope typ in
  (* Rename _ to generated name, so we can see the difference *)
  let counter = ref (-1) in
  let tele =
    List.map
      (fun bind ->
         incr counter;
         { bind with
           name = (if bind.name = "_" then "x" ^ string_of_int !counter else bind.name)
         })
      tele
  in
  (* If the dependencies of the constructor are the inductive type itself, find out and create recursive motives *)
  let recursive_points =
    List.filter
      (fun bind ->
         let typ = bind.bound in
         let typ = check_type ~loc typ in
         let typ = eval typ in
         match typ with
         | IndType (head, _) -> head == ind_name
         | _ -> false)
      tele
  in
  let motives =
    List.map
      (fun { name; _ } ->
         { name = "fix"
         ; bound = Surface.apply (Var motive_name) [ Var name ]
         ; implicit = false
         })
      recursive_points
  in
  (* Make the current case binder *)
  { name = "case-" ^ name
  ; bound =
      List.fold_right
        (fun bind result -> Surface.Pi (bind, result))
        (List.append tele motives)
        (Surface.apply
           (Var motive_name)
           [ (if List.is_empty tele
              then Var name
              else
                (* we apply to a telescope so each implicit/explicit call is right *)
                Surface.apply_tele (Var name) tele)
           ])
  ; implicit = false
  }
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
    (fun library ->
       (Context.S.modify_visible
        @@ Yuujinchou.Language.(union [ all; renaming library [] ]));
       Env.S.modify_visible @@ Yuujinchou.Language.(union [ all; renaming library [] ]))
    file.imports;
  List.iter
    (fun (top : Surface.top Asai.Range.located) ->
       let loc = Option.get top.loc in
       check_top ~loc top.value)
    file.tops

and check_top ~loc top =
  match top with
  | Surface.Data { name; params; ind_ty; clauses } ->
    handle_inductive_type ~loc name params ind_ty clauses
  | Surface.Let (name, bindings, result_ty, body) ->
    let typ : Surface.pretype =
      List.fold_right
        (fun binding return_ty -> Surface.Pi (binding, return_ty))
        bindings
        result_ty
    in
    Reporter.tracef ~loc "checking [top let] %s : %s" name ([%show: Surface.pretype] typ)
    @@ fun () ->
    let typ = check_type ~loc typ in
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

and handle_inductive_type ~loc name_of_the_inductive_type params ind_ty clauses =
  Reporter.tracef ~loc "checking [inductive data type] %s" name_of_the_inductive_type
  @@ fun () ->
  (* Bind type former into context and environment *)
  let typ : Surface.pretype =
    List.fold_right
      (fun binding return_ty -> Surface.Pi (binding, return_ty))
      params
      ind_ty
  in
  let typ = check_type ~loc typ in
  let typ = eval typ in
  Context.S.include_singleton
    ~context_visible:`Visible
    ~context_export:`Export
    ([ name_of_the_inductive_type ], (typ, `Local));
  Env.S.include_singleton
    ~context_visible:`Visible
    ~context_export:`Export
    ( [ name_of_the_inductive_type ]
    , (IndType (name_of_the_inductive_type, Bwd.Emp), `Local) );
  (* Create each type introducer *)
  List.iter (bind_constructor ~loc) clauses;
  (* Build type eliminator (or induction principle) *)
  (* 先從 ind_ty = U 沒有 params 的情況思考，那 motive 就是 D -> U *)
  let handle_name = "x" in
  let ind_deps = List.map (fun b -> { b with implicit = true }) params in
  (* If parameters is empty, e.g. `Nat`, then we use `Nat`
     or we have parameters, e.g. List A, then we use `List A` *)
  let ind_typ = Surface.apply_tele (Var name_of_the_inductive_type) params in
  let motive_typ : Surface.pretype =
    Surface.pi
      [ { name = handle_name; bound = ind_typ; implicit = false } ]
      Surface.Universe
  in
  let motive_bound_name = "P" in
  let lst_of_case_typ : Surface.pretype binder list =
    List.map (bind_of_case ~loc name_of_the_inductive_type motive_bound_name) clauses
  in
  let typ : Surface.pretype =
    List.fold_right
      (fun binding return_ty -> Surface.Pi (binding, return_ty))
      (List.append
         ind_deps
         ({ name = motive_bound_name; bound = motive_typ; implicit = false }
          :: lst_of_case_typ))
      (* The final part is just a (x : D) -> P x
        where
        1. D is the inductive data type
        2. P is the motive
      *)
      (Surface.pi
         [ { name = handle_name; bound = ind_typ; implicit = false } ]
         (Surface.apply (Var motive_bound_name) [ Var handle_name ]))
  in
  let eliminator_name = name_of_the_inductive_type ^ "-elim" in
  Eio.traceln "ELIMINATOR %s : %s\n" eliminator_name ([%show: Surface.pretype] typ);
  let typ = check ~loc typ Universe in
  let typ = eval typ in
  (* TODO: insert computation of eliminator into Environment *)
  Context.S.include_singleton
    ~context_visible:`Visible
    ~context_export:`Export
    ([ eliminator_name ], (typ, `Local))
;;
