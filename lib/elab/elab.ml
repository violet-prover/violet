include Elab_common
open Violet_surface
open Violet_common
open Syntax
open Asai.Range
open Bwd

(* [ty] 是 implicit Pi
   但 [term] 不是 implicit lambda 時
   1. 安插 `\{x} => ...` 在前面
   2. 重新檢查 [term] 作為 implicit Pi 的 body 可不可行 *)
let try_insert_implicit_abstraction
      (m : machine)
      (loc : Asai.Range.t)
      (term : Surface.preterm)
      (ty : Core.value_ty)
  : bool
  =
  match Evaluation.force_head ty with
  | Core.VPi ({ name = pi_name; bound = a; implicit = true }, b)
    when match term with
         | Lambda { implicit = true; _ } -> false
         | _ -> true ->
    let body_ty = b (Core.RigidLocal (m.ctx.lvl, Bwd.Emp)) in
    save_ctx m;
    m.ctx <- bind m.ctx pi_name a;
    push m (KLam_Body (loc, pi_name, true));
    push m (GCheck (loc, term, body_ty));
    true
  | _ -> false
;;

let rec dispatch (m : machine) (g : goal) : unit =
  match g with
  | GInfer (loc, Located { loc = loc'; value }) ->
    push m (GInfer (Option.get loc', value));
    ignore loc
  | GCheck (loc, Located { loc = loc'; value }, ty) ->
    push m (GCheck (Option.get loc', value, ty));
    ignore loc
  | GCheck (loc, term, ty) when try_insert_implicit_abstraction m loc term ty -> ()
  | GInferType (loc, Located { loc = loc'; value }) ->
    push m (GInferType (Option.get loc', value));
    ignore loc
  | GInfer (_, Universe) ->
    m.result
    <- Some
         (PTermType (Core.Universe Level.LZero, Core.Universe (Level.LSuc Level.LZero)))
  | GInfer (loc, Var [ x ]) ->
    (match resolve_local m.ctx x with
     | Some i ->
       let ty = local_type m.ctx i in
       let pp_ty = Pretty.pp_term (view_of_ctx m.ctx) (Evaluation.quote m.ctx.lvl ty) in
       Observer.emit (Use { path = [ x ]; loc; def_loc = None; ty; pp_ty });
       m.result <- Some (PTermType (Core.LocalVar i, ty))
     | None ->
       (match resolve_universe_var x with
        | Some l ->
          let ty = Core.Universe (Level.lsuc l) in
          let pp_ty =
            Pretty.pp_term (view_of_ctx m.ctx) (Evaluation.quote m.ctx.lvl ty)
          in
          Observer.emit (Use { path = [ x ]; loc; def_loc = None; ty; pp_ty });
          m.result <- Some (PTermType (Core.Universe l, ty))
        | None ->
          let ty = Context.lookup x in
          let pp_ty =
            Pretty.pp_term (view_of_ctx m.ctx) (Evaluation.quote m.ctx.lvl ty)
          in
          Observer.emit (Use { path = [ x ]; loc; def_loc = None; ty; pp_ty });
          m.result <- Some (PTermType (Core.Var x, ty))))
  | GInfer (loc, Var path) ->
    let ty = Context.lookup_path path in
    let joined = String.concat "/" path in
    let pp_ty = Pretty.pp_term (view_of_ctx m.ctx) (Evaluation.quote m.ctx.lvl ty) in
    Observer.emit (Use { path; loc; def_loc = None; ty; pp_ty });
    m.result <- Some (PTermType (Core.Var joined, ty))
  | GInferType (loc, Goal name_opt) ->
    let name = resolve_goal_name m name_opt in
    emit_goal_report ~loc m ~name ~target:(Core.Universe Level.LZero);
    incr m.pending_goals;
    m.result <- Some (PType (Meta.fresh_goal m.ctx.lvl, Level.LZero))
  | GInferType (loc, p) ->
    push m (KEnsureUniverse loc);
    push m (GInfer (loc, p))
  | KEnsureUniverse loc ->
    (match take_result m with
     | PTermType (tm, ty) ->
       (match Evaluation.force_head ty with
        | Core.Universe l -> m.result <- Some (PType (tm, l))
        | other ->
          Reporter.fatalf
            ~loc
            Type_error
            "expected a type, but got `%s : %s`"
            (Pretty.pp_term (view_of_ctx m.ctx) tm)
            (Pretty.pp_term (view_of_ctx m.ctx) (Evaluation.quote m.ctx.lvl other)))
     | other ->
       Reporter.fatalf
         Elab_error
         "KEnsureUniverse: bad result %s"
         ([%show: produced] other))
  | GInfer (loc, Pi ({ name; bound = a; implicit }, b)) ->
    push m (KPi_HaveDom (loc, name, implicit, b));
    push m (GInferType (loc, a))
  | KPi_HaveDom (loc, name, implicit, body) ->
    (match take_result m with
     | PType (a_tm, l_a) ->
       let a_val = Evaluation.eval m.ctx.env a_tm in
       save_ctx m;
       m.ctx <- bind m.ctx name a_val;
       push m (KPi_HaveCod (loc, name, implicit, a_tm, l_a));
       push m (GInferType (loc, body))
     | other ->
       Reporter.fatalf Elab_error "KPi_HaveDom: bad result %s" ([%show: produced] other))
  | KPi_HaveCod (_loc, name, implicit, a_tm, l_a) ->
    (match take_result m with
     | PType (b_tm, l_b) ->
       restore_ctx m;
       m.result
       <- Some
            (PTermType
               ( Core.Pi ({ name; bound = a_tm; implicit }, b_tm)
               , Core.Universe (Level.lmax l_a l_b) ))
     | other ->
       Reporter.fatalf Elab_error "KPi_HaveCod: bad result %s" ([%show: produced] other))
  | GCheck (loc, Lambda { name; bound = body; implicit = lambda_mode }, ty) ->
    (match Evaluation.force_head ty with
     | Core.VPi ({ name = _; bound = a; implicit = pi_mode }, b) ->
       if lambda_mode <> pi_mode
       then Reporter.fatalf ~loc Elab_error "mode mismatching"
       else begin
         let body_ty = b (Core.RigidLocal (m.ctx.lvl, Bwd.Emp)) in
         save_ctx m;
         m.ctx <- bind m.ctx name a;
         push m (KLam_Body (loc, name, lambda_mode));
         push m (GCheck (loc, body, body_ty))
       end
     | _ ->
       let ty = Pretty.pp_term (view_of_ctx m.ctx) (Evaluation.quote m.ctx.lvl ty) in
       Reporter.fatalf ~loc Elab_error "Lambda checked against non-Pi: %s" ty)
  | KLam_Body (_loc, name, implicit) ->
    (match take_result m with
     | PTerm body_tm ->
       restore_ctx m;
       m.result <- Some (PTerm (Core.Lambda { name; bound = body_tm; implicit }))
     | other ->
       Reporter.fatalf Elab_error "KLam_Body: bad result %s" ([%show: produced] other))
  | GInfer (loc, TypedLambda ({ name; bound = ty; implicit }, body)) ->
    push m (KTypedLam_HaveDom (loc, name, implicit, body));
    push m (GInferType (loc, ty))
  | KTypedLam_HaveDom (loc, name, implicit, body) ->
    (match take_result m with
     | PType (ty_tm, _) ->
       let ty_val = Evaluation.eval m.ctx.env ty_tm in
       save_ctx m;
       m.ctx <- bind m.ctx name ty_val;
       push m (KTypedLam_HaveBody (loc, name, implicit, ty_tm, ty_val));
       push m (GInfer (loc, body))
     | other ->
       Reporter.fatalf
         Elab_error
         "KTypedLam_HaveDom: bad result %s"
         ([%show: produced] other))
  | KTypedLam_HaveBody (_loc, name, implicit, ty_tm, ty_val) ->
    (match take_result m with
     | PTermType (body_tm, body_ty) ->
       restore_ctx m;
       m.result
       <- Some
            (PTermType
               ( Core.TypedLambda ({ name; bound = ty_tm; implicit }, body_tm)
               , Core.VPi ({ name; bound = ty_val; implicit }, fun _ -> body_ty) ))
     | other ->
       Reporter.fatalf
         Elab_error
         "KTypedLam_HaveBody: bad result %s"
         ([%show: produced] other))
  | GInfer (loc, App (is_implicit, f, arg)) ->
    push m (KApp_HaveFn (loc, is_implicit, arg));
    push m (GInfer (loc, f))
  | KApp_HaveFn (loc, is_implicit, arg) ->
    (match take_result m with
     | PTermType (f_tm, f_ty) ->
       (match Evaluation.force_head f_ty with
        | Core.VPi ({ implicit; name = pi_name; bound = a }, b) ->
          if is_implicit = implicit
          then begin
            push m (KApp_HaveArg (loc, f_tm, b));
            push m (GCheck (loc, arg, a))
          end
          else if implicit
          then begin
            (* Insert a fresh implicit meta on the f side, then retry. *)
            let display =
              Printf.sprintf
                "{%s : %s}"
                (Syntax.Name.to_string pi_name)
                (Pretty.pp_term (view_of_ctx m.ctx) (Evaluation.quote m.ctx.lvl a))
            in
            let meta_tm = Meta.meta_fresh_with m.ctx.lvl ~origin:{ loc; display } in
            let meta_val = Evaluation.eval m.ctx.env meta_tm in
            let new_f_tm = Core.App (f_tm, meta_tm) in
            let new_f_ty = b meta_val in
            m.result <- Some (PTermType (new_f_tm, new_f_ty));
            push m (KApp_HaveFn (loc, is_implicit, arg))
          end
          else
            Reporter.fatalf
              ~loc
              Elab_error
              "Bad apply at %s"
              (Pretty.pp_term (view_of_ctx m.ctx) f_tm)
        | ty ->
          let ty = Pretty.pp_term (view_of_ctx m.ctx) (Evaluation.quote m.ctx.lvl ty) in
          Reporter.fatalf
            ~loc
            Type_error
            "cannot apply to `(%s) : %s`"
            (Pretty.pp_term (view_of_ctx m.ctx) f_tm)
            ty)
     | other ->
       Reporter.fatalf Elab_error "KApp_HaveFn: bad result %s" ([%show: produced] other))
  | KApp_HaveArg (_loc, f_tm, b) ->
    (match take_result m with
     | PTerm arg_tm ->
       let arg_val = Evaluation.eval m.ctx.env arg_tm in
       m.result <- Some (PTermType (Core.App (f_tm, arg_tm), b arg_val))
     | other ->
       Reporter.fatalf Elab_error "KApp_HaveArg: bad result %s" ([%show: produced] other))
  | GInfer (loc, Op_soup _) | GCheck (loc, Op_soup _, _) ->
    Reporter.fatalf
      ~loc
      Elab_error
      "internal: Op_soup reached elaborator (resolver should have lowered it)"
  | GInfer (loc, RecordLit _) -> Elab_record.handle_infer_record_lit m loc
  | GCheck (loc, RecordLit entries, expected_ty) ->
    Elab_record.handle_check_record_lit m loc entries expected_ty
  | KRecordLit_Field
      ( loc
      , r_name
      , done_rev
      , current_fname
      , remaining_entries
      , remaining_term_binders
      , eval_env ) ->
    Elab_record.handle_record_lit_field
      m
      loc
      r_name
      done_rev
      current_fname
      remaining_entries
      remaining_term_binders
      eval_env
  | GInfer (loc, RecordUpdate _) -> Elab_record.handle_infer_record_update m loc
  | GCheck (loc, RecordUpdate (base, overrides), expected_ty) ->
    Elab_record.handle_check_record_update m loc base overrides expected_ty
  | KRecordUpdate_HaveBase (loc, r_name, overrides, term_fields, field_env) ->
    Elab_record.handle_record_update_have_base
      m
      loc
      r_name
      overrides
      term_fields
      field_env
  | KRecordUpdate_Field
      ( loc
      , r_name
      , base_core
      , overrides
      , done_rev
      , current_fname
      , remaining_term_fields
      , eval_env ) ->
    Elab_record.handle_record_update_field
      m
      loc
      r_name
      base_core
      overrides
      done_rev
      current_fname
      remaining_term_fields
      eval_env
  | GInfer (loc, Proj (e, f)) -> Elab_record.handle_infer_proj m loc e f
  | KProj_HaveRec (loc, f) -> Elab_record.handle_proj_have_rec m loc f
  | GInfer (loc, Lambda _) -> Reporter.fatalf ~loc Elab_error "cannot infer lambda term"
  | GCheck (_loc, Hole, _) -> m.result <- Some (PTerm (Meta.meta_fresh m.ctx.lvl))
  | GInfer (_loc, Hole) ->
    let ty = Evaluation.eval m.ctx.env (Meta.meta_fresh m.ctx.lvl) in
    let tm = Meta.meta_fresh m.ctx.lvl in
    m.result <- Some (PTermType (tm, ty))
  | GCheck (loc, Inline_elim d, ty) ->
    Elab_elim.handle_check_inline_elim ~infer_term m loc d ty
  | GInfer (loc, Inline_elim _) ->
    Reporter.fatalf ~loc Elab_error "cannot infer the type of a nested `<= \\elim`"
  | GCheck (loc, Goal name_opt, ty) ->
    let name = resolve_goal_name m name_opt in
    emit_goal_report ~loc m ~name ~target:ty;
    incr m.pending_goals;
    m.result <- Some (PTerm (Meta.fresh_goal m.ctx.lvl))
  | GInfer (loc, Goal name_opt) ->
    let name = resolve_goal_name m name_opt in
    let ty_tm = Meta.fresh_goal m.ctx.lvl in
    let ty_val = Evaluation.eval m.ctx.env ty_tm in
    emit_goal_report ~loc m ~name ~target:ty_val;
    incr m.pending_goals;
    m.result <- Some (PTermType (Meta.fresh_goal m.ctx.lvl, ty_val))
  | GInfer (loc, Max (a, b)) ->
    push m (KMax_HaveLeft (loc, b));
    push m (GInfer (loc, a))
  | KMax_HaveLeft (loc, b) ->
    (match take_result m with
     | PTermType (Core.Universe l_a, _) ->
       push m (KMax_HaveRight (loc, l_a));
       push m (GInfer (loc, b))
     | PTermType (other_tm, _) ->
       Reporter.fatalf
         ~loc
         Type_error
         "operands of `⊔` must be universes, got `%s`"
         (Pretty.pp_term (view_of_ctx m.ctx) other_tm)
     | other ->
       Reporter.fatalf Elab_error "KMax_HaveLeft: bad result %s" ([%show: produced] other))
  | KMax_HaveRight (loc, l_a) ->
    (match take_result m with
     | PTermType (Core.Universe l_b, _) ->
       let l = Level.lmax l_a l_b in
       m.result <- Some (PTermType (Core.Universe l, Core.Universe (Level.lsuc l)))
     | PTermType (other_tm, _) ->
       Reporter.fatalf
         ~loc
         Type_error
         "operands of `⊔` must be universes, got `%s`"
         (Pretty.pp_term (view_of_ctx m.ctx) other_tm)
     | other ->
       Reporter.fatalf
         Elab_error
         "KMax_HaveRight: bad result %s"
         ([%show: produced] other))
  | GInfer (loc, IdAbsurd p) ->
    push m (KIdAbsurd_HaveArg loc);
    push m (GInfer (loc, p))
  | KIdAbsurd_HaveArg loc ->
    (match take_result m with
     | PTermType (p_tm, p_ty) ->
       (* Verify p_ty is `Id <A> <c1 args> <c2 args>` with c1 ≠ c2 (same
          inductive, i.e. constructors of the underlying `A`). The spine
          shape is set by the Id data declaration; we read positions 1 and
          2 of the spine for the two Id arguments. *)
       (match Evaluation.force_head p_ty with
        | Core.IndType (ind_name, spine) when String.equal ind_name "Id" ->
          let xs = Bwd.to_list spine in
          if List.length xs < 3
          then
            Reporter.fatalf
              ~loc
              Elab_error
              "\\absurd-id: Id-typed argument has unexpected spine length %d"
              (List.length xs);
          let lhs =
            match List.nth_opt xs (List.length xs - 2) with
            | Some v -> v
            | None ->
              Reporter.fatalf
                ~loc
                Elab_error
                "\\absurd-id: cannot read lhs from Id spine (len=%d)"
                (List.length xs)
          in
          let rhs =
            match List.nth_opt xs (List.length xs - 1) with
            | Some v -> v
            | None ->
              Reporter.fatalf
                ~loc
                Elab_error
                "\\absurd-id: cannot read rhs from Id spine (len=%d)"
                (List.length xs)
          in
          (match Evaluation.force_head lhs, Evaluation.force_head rhs with
           | Core.Label (c1, _), Core.Label (c2, _) when not (String.equal c1 c2) ->
             let empty_ty = Core.IndType ("Empty", Bwd.Emp) in
             m.result <- Some (PTermType (Core.IdAbsurd p_tm, empty_ty))
           | l, r ->
             Reporter.fatalf
               ~loc
               Elab_error
               "\\absurd-id: expected Id of distinct-ctor-headed values, got `Id _ %s %s`"
               (Pretty.pp_term (view_of_ctx m.ctx) (Evaluation.quote m.ctx.lvl l))
               (Pretty.pp_term (view_of_ctx m.ctx) (Evaluation.quote m.ctx.lvl r)))
        | other ->
          Reporter.fatalf
            ~loc
            Elab_error
            "\\absurd-id: argument is not Id-typed, got `%s`"
            (Pretty.pp_term (view_of_ctx m.ctx) (Evaluation.quote m.ctx.lvl other)))
     | other ->
       Reporter.fatalf
         Elab_error
         "KIdAbsurd_HaveArg: bad result %s"
         ([%show: produced] other))
  | GCheck (loc, Var [ x ], expected) when Option.is_none (resolve_local m.ctx x) ->
    (* Type-directed resolution: if expected forces to IndType(ind, _) and
       [ind; x] is bound in Context, use the namespaced binding.
       Otherwise fall through to standard inference. *)
    let head = Evaluation.force_head expected in
    (match head with
     | Core.IndType (ind, _) when Context.has_path [ ind; x ] ->
       (* Build the namespaced term: kernel eval resolves "ind/x" via E.lookup *)
       let ty = Context.lookup_path [ ind; x ] in
       let tm : Core.term = Core.Var (ind ^ "/" ^ x) in
       push m (KCheckBy_Infer (loc, expected));
       m.result <- Some (PTermType (tm, ty))
     | _ ->
       push m (KCheckBy_Infer (loc, expected));
       push m (GInfer (loc, Var [ x ])))
  | GCheck (loc, other, expected) ->
    push m (KCheckBy_Infer (loc, expected));
    push m (GInfer (loc, other))
  | KCheckBy_Infer (loc, expected) ->
    (match take_result m with
     | PTermType (tm, infer_ty) ->
       let rec insert_implicit_apps tm ty =
         match Evaluation.force_head ty with
         | Core.VPi ({ implicit = true; name = pi_name; bound = a }, b) ->
           let display =
             Printf.sprintf
               "{%s : %s}"
               (Syntax.Name.to_string pi_name)
               (Pretty.pp_term (view_of_ctx m.ctx) (Evaluation.quote m.ctx.lvl a))
           in
           let meta_tm = Meta.meta_fresh_with m.ctx.lvl ~origin:{ loc; display } in
           let meta_val = Evaluation.eval m.ctx.env meta_tm in
           insert_implicit_apps (Core.App (tm, meta_tm)) (b meta_val)
         | _ -> tm, ty
       in
       let tm, infer_ty = insert_implicit_apps tm infer_ty in
       (match Evaluation.force_head expected, Evaluation.force_head infer_ty with
        | Core.Universe l1, Core.Universe l2 when Level.not_equal l1 l2 && Level.le l2 l1
          -> m.result <- Some (PTerm (Core.Lift { from_lvl = l2; to_lvl = l1; ty = tm }))
        | _ ->
          Unification.unify ~loc (view_of_ctx m.ctx) expected infer_ty;
          m.result <- Some (PTerm tm))
     | other ->
       Reporter.fatalf
         Elab_error
         "KCheckBy_Infer: bad result %s"
         ([%show: produced] other))
  | GTopUniverseDecl names -> Elab_decl.handle_universe_decl m names
  | GTopLet { loc; name; name_loc; bindings; result_ty; body } ->
    Elab_decl.handle_top_let m ~loc ~name ~name_loc ~bindings ~result_ty ~body
  | KTopLet_HaveType { loc; name; name_loc; body; bindings } ->
    Elab_decl.handle_top_let_have_type m ~loc ~name ~name_loc ~body ~bindings
  | KTopLet_HaveBody { loc; name; name_loc; typ_tm; typ_val } ->
    Elab_decl.handle_top_let_have_body m ~loc ~name ~name_loc ~typ_tm ~typ_val
  | KTopElimDef_HaveBody { loc; name; name_loc; typ_tm; typ_val; func_name; target_pos }
    ->
    Elab_elim.handle_elim_def_have_body
      m
      ~loc
      ~name
      ~name_loc
      ~typ_tm
      ~typ_val
      ~func_name
      ~target_pos
  | GTopStackDef { loc; name; name_loc; bindings; result_ty; moves; clauses } ->
    Elab_elim.handle_stack_def m ~loc ~name ~name_loc ~bindings ~result_ty ~moves ~clauses
  | KTopStackDef_HaveType { loc; name; name_loc; bindings; signature; moves; clauses } ->
    Elab_elim.handle_stack_def_have_type
      m
      ~loc
      ~name
      ~name_loc
      ~bindings
      ~signature
      ~moves
      ~clauses
  | GTopElimDef
      { loc; name; name_loc; bindings; result_ty; opens; intros; target; clauses } ->
    Elab_elim.handle_elim_def
      m
      ~loc
      ~name
      ~name_loc
      ~bindings
      ~result_ty
      ~opens
      ~intros
      ~target
      ~clauses
  | KTopElimDef_HaveType
      { loc; name; name_loc; bindings; signature; opens; intros; target; clauses } ->
    Elab_elim.handle_elim_def_have_type
      m
      ~loc
      ~name
      ~name_loc
      ~bindings
      ~signature
      ~opens
      ~intros
      ~target
      ~clauses
  | GTopData (loc, data) -> Elab_data.handle_top_data m loc data
  | KTopData_HaveType { loc; name; name_loc; params; deps; ind_ty; ctors; ctor_name_locs }
    ->
    Elab_data.handle_top_data_have_type
      ~check_type
      ~check_term_against
      m
      ~loc
      ~name
      ~name_loc
      ~params
      ~deps
      ~ind_ty
      ~ctors
      ~ctor_name_locs
  | GTopRecord (loc, Surface.Record { name; params; ind_ty; fields; _ }) ->
    Elab_record.handle_top_record m loc name params ind_ty fields
  | GTopRecord (_, _) -> Elab_record.handle_top_record_error m
  | KTopRecord_HaveType (loc, name, params, ind_ty, fields) ->
    Elab_record.handle_top_record_have_type ~check_type m loc name params ind_ty fields

and drive (m : machine) : produced =
  match m.goals with
  | [] -> take_result m
  | g :: rest ->
    m.goals <- rest;
    dispatch m g;
    drive m

and infer_type ~loc (ctx : local_ctx) (pretype : Surface.pretype)
  : Core.term * Level.level
  =
  let m =
    make_machine
      ~module_name:"_internal"
      ~kernel_module:(Violet_kernel.Module.create ())
      ~goal_counter:(ref 0)
      ~is_exported:(fun _ -> false)
      ()
  in
  m.ctx <- ctx;
  push m (GInferType (loc, pretype));
  match drive m with
  | PType (tm, l) -> tm, l
  | other -> Reporter.fatalf ~loc Elab_error "infer_type: %s" ([%show: produced] other)

and check_type ~loc (ctx : local_ctx) (pretype : Surface.pretype) : Core.term =
  fst (infer_type ~loc ctx pretype)

and check_term_against ~loc (ctx : local_ctx) (term : Surface.preterm) (ty : Core.value)
  : Core.term
  =
  let m =
    make_machine
      ~module_name:"_internal"
      ~kernel_module:(Violet_kernel.Module.create ())
      ~goal_counter:(ref 0)
      ~is_exported:(fun _ -> false)
      ()
  in
  m.ctx <- ctx;
  push m (GCheck (loc, term, ty));
  match drive m with
  | PTerm tm -> tm
  | other ->
    Reporter.fatalf ~loc Elab_error "check_term_against: %s" ([%show: produced] other)

and infer_term ~loc (ctx : local_ctx) (term : Surface.preterm) : Core.term * Core.value =
  let m =
    make_machine
      ~module_name:"_internal"
      ~kernel_module:(Violet_kernel.Module.create ())
      ~goal_counter:(ref 0)
      ~is_exported:(fun _ -> false)
      ()
  in
  m.ctx <- ctx;
  push m (GInfer (loc, term));
  match drive m with
  | PTermType (tm, ty) -> tm, ty
  | other -> Reporter.fatalf ~loc Elab_error "infer_term: %s" ([%show: produced] other)
;;

let with_handlers (k : unit -> 'a) : 'a =
  Reporter.run
    ~emit:(fun _ -> ())
    ~fatal:(fun d -> failwith ([%show: Reporter.Message.t] d.message))
  @@ fun () ->
  Observer.run_silent
  @@ fun () ->
  Context.S.run
    ~shadow:Context.Handler.shadow
    ~not_found:Context.Handler.not_found
    ~hook:Context.Handler.hook
  @@ fun () ->
  Env.S.run
    ~shadow:Env.Handler.shadow
    ~not_found:Env.Handler.not_found
    ~hook:Env.Handler.hook
  @@ k
;;

(* Like with_handlers, but prints emitted diagnostics to stdout so that
   %expect_test blocks can match against them. *)
let with_handlers_emitting (k : unit -> 'a) : 'a =
  Reporter.run
    ~emit:(fun (d : Reporter.Message.t Asai.Diagnostic.t) ->
      Format.printf "[%s] %t@." (Reporter.Message.show d.message) d.explanation.value)
    ~fatal:(fun d -> failwith ([%show: Reporter.Message.t] d.message))
  @@ fun () ->
  Observer.run_silent
  @@ fun () ->
  Context.S.run
    ~shadow:Context.Handler.shadow
    ~not_found:Context.Handler.not_found
    ~hook:Context.Handler.hook
  @@ fun () ->
  Env.S.run
    ~shadow:Env.Handler.shadow
    ~not_found:Env.Handler.not_found
    ~hook:Env.Handler.hook
  @@ k
;;

let infer_for_test (p : Surface.preterm) : Core.term * Core.value =
  with_handlers
  @@ fun () ->
  let m =
    make_machine
      ~module_name:"test"
      ~kernel_module:(Violet_kernel.Module.create ())
      ~goal_counter:(ref 0)
      ()
  in
  push m (GInfer (Asai.Range.of_lex_range (Lexing.dummy_pos, Lexing.dummy_pos), p));
  match drive m with
  | PTermType (tm, ty) -> tm, ty
  | other -> Reporter.fatalf Elab_error "infer_for_test: got %s" ([%show: produced] other)
;;

let%expect_test "infer Universe" =
  let tm, ty = infer_for_test Surface.Universe in
  Printf.printf "%s : %s" ([%show: Core.term] tm) ([%show: Core.value] ty);
  [%expect {| universe 𝓤₀ : universe (𝓤₀+1) |}]
;;

let%expect_test "infer Var bound locally" =
  with_handlers (fun () ->
    let m =
      make_machine
        ~module_name:"test"
        ~kernel_module:(Violet_kernel.Module.create ())
        ~goal_counter:(ref 0)
        ()
    in
    m.ctx <- bind m.ctx (Syntax.Named "x") (Core.Universe Level.LZero);
    push
      m
      (GInfer
         ( Asai.Range.of_lex_range (Lexing.dummy_pos, Lexing.dummy_pos)
         , Surface.Var [ "x" ] ));
    let tm, ty =
      match drive m with
      | PTermType (a, b) -> a, b
      | _ -> failwith "wrong shape"
    in
    Printf.printf "%s : %s" ([%show: Core.term] tm) ([%show: Core.value] ty));
  [%expect {| $0 : universe 𝓤₀ |}]
;;

(* `_` written by the user is an ordinary `Named "_"` binder, fully
   referenceable. *)
let%expect_test "user `_` binder is a normal name and can be referenced" =
  with_handlers (fun () ->
    let m =
      make_machine
        ~module_name:"test"
        ~kernel_module:(Violet_kernel.Module.create ())
        ~goal_counter:(ref 0)
        ()
    in
    m.ctx <- bind m.ctx (Syntax.Named "_") (Core.Universe Level.LZero);
    push
      m
      (GInfer
         ( Asai.Range.of_lex_range (Lexing.dummy_pos, Lexing.dummy_pos)
         , Surface.Var [ "_" ] ));
    let tm, ty =
      match drive m with
      | PTermType (a, b) -> a, b
      | _ -> failwith "wrong shape"
    in
    Printf.printf "%s : %s" ([%show: Core.term] tm) ([%show: Core.value] ty));
  [%expect {| $0 : universe 𝓤₀ |}]
;;

(* `Anon` binders (e.g. fabricated by the parser for arrow types) carry no
   string name; surface name lookup of `_` cannot capture them. *)
let%expect_test "var lookup of `_` ignores Anon binders" =
  (try
     with_handlers (fun () ->
       let m =
         make_machine
           ~module_name:"test"
           ~kernel_module:(Violet_kernel.Module.create ())
           ~goal_counter:(ref 0)
           ()
       in
       m.ctx <- bind m.ctx Syntax.Anon (Core.Universe Level.LZero);
       push
         m
         (GInfer
            ( Asai.Range.of_lex_range (Lexing.dummy_pos, Lexing.dummy_pos)
            , Surface.Var [ "_" ] ));
       let _ = drive m in
       print_endline "UNEXPECTED: `_` resolved")
   with
   | Failure msg -> Printf.printf "rejected: %s" msg);
  [%expect {| rejected: Reporter.Message.NoVar_error |}]
;;

let%expect_test "infer Pi" =
  let p =
    Surface.Pi
      ({ name = Named "x"; bound = Surface.Universe; implicit = false }, Surface.Universe)
  in
  let tm, ty = infer_for_test p in
  Printf.printf "%s : %s" ([%show: Core.term] tm) ([%show: Core.value] ty);
  [%expect {| ∀ (x : universe 𝓤₀) -> universe 𝓤₀ : universe (𝓤₀+1) ⊔ (𝓤₀+1) |}]
;;

let%expect_test "check Lambda against Pi" =
  let p =
    Surface.Lambda { name = Named "x"; bound = Surface.Var [ "x" ]; implicit = false }
  in
  let expected_ty =
    Core.VPi
      ( { name = Named "x"; bound = Core.Universe Level.LZero; implicit = false }
      , fun _ -> Core.Universe Level.LZero )
  in
  with_handlers (fun () ->
    let m =
      make_machine
        ~module_name:"test"
        ~kernel_module:(Violet_kernel.Module.create ())
        ~goal_counter:(ref 0)
        ()
    in
    push
      m
      (GCheck
         (Asai.Range.of_lex_range (Lexing.dummy_pos, Lexing.dummy_pos), p, expected_ty));
    let tm =
      match drive m with
      | PTerm t -> t
      | _ -> failwith "wrong shape"
    in
    Printf.printf "%s" ([%show: Core.term] tm));
  [%expect {| fun x => $0 |}]
;;

let%expect_test "infer App" =
  (* Apply a locally-bound function f : (U -> U) to a locally-bound argument x : U.
     This tests the App dispatch without needing lift insertion. *)
  with_handlers (fun () ->
    let m =
      make_machine
        ~module_name:"test"
        ~kernel_module:(Violet_kernel.Module.create ())
        ~goal_counter:(ref 0)
        ()
    in
    let loc = Asai.Range.of_lex_range (Lexing.dummy_pos, Lexing.dummy_pos) in
    m.ctx <- bind m.ctx (Syntax.Named "x") (Core.Universe Level.LZero);
    let f_ty =
      Core.VPi
        ( { name = Named "a"; bound = Core.Universe Level.LZero; implicit = false }
        , fun _ -> Core.Universe Level.LZero )
    in
    m.ctx <- bind m.ctx (Syntax.Named "f") f_ty;
    push m (GInfer (loc, Surface.App (false, Surface.Var [ "f" ], Surface.Var [ "x" ])));
    match drive m with
    | PTermType (tm, ty) ->
      Printf.printf "tm: %s\nty: %s" ([%show: Core.term] tm) ([%show: Core.value] ty)
    | _ -> failwith "wrong shape");
  [%expect
    {|
    tm: $0 $1
    ty: universe 𝓤₀
    |}]
;;

let%expect_test "report named goal in check mode" =
  with_handlers_emitting (fun () ->
    let m =
      make_machine
        ~module_name:"nat"
        ~kernel_module:(Violet_kernel.Module.create ())
        ~goal_counter:(ref 0)
        ()
    in
    m.ctx <- bind m.ctx (Syntax.Named "A") (Core.Universe Level.LZero);
    m.ctx <- bind m.ctx (Syntax.Named "x") (Core.RigidLocal (0, Bwd.Emp));
    push
      m
      (GCheck
         ( Asai.Range.of_lex_range (Lexing.dummy_pos, Lexing.dummy_pos)
         , Surface.Goal (Some "here")
         , Core.RigidLocal (0, Bwd.Emp) ));
    ignore (drive m);
    Printf.printf "pending=%d" !(m.pending_goals));
  [%expect
    {|
    [Reporter.Message.Goal_report] nat/?here
      --- context ---
      A : universe 𝓤₀
      x : A
      --- target ---
      A
    pending=1
    |}]
;;

let%expect_test "auto-numbered goals" =
  with_handlers_emitting (fun () ->
    let counter = ref 0 in
    let m =
      make_machine
        ~module_name:"nat"
        ~kernel_module:(Violet_kernel.Module.create ())
        ~goal_counter:counter
        ()
    in
    push
      m
      (GCheck
         ( Asai.Range.of_lex_range (Lexing.dummy_pos, Lexing.dummy_pos)
         , Surface.Goal None
         , Core.Universe Level.LZero ));
    push
      m
      (GCheck
         ( Asai.Range.of_lex_range (Lexing.dummy_pos, Lexing.dummy_pos)
         , Surface.Goal None
         , Core.Universe Level.LZero ));
    ignore (drive m);
    Printf.printf "pending=%d counter=%d" !(m.pending_goals) !counter);
  [%expect
    {|
    [Reporter.Message.Goal_report] nat/?0
      --- context ---
      --- target ---
      universe 𝓤₀
    [Reporter.Message.Goal_report] nat/?1
      --- context ---
      --- target ---
      universe 𝓤₀
    pending=2 counter=2
    |}]
;;

let check_top
      ~(module_name : string)
      ~(kernel_module : Violet_kernel.Module.t)
      ~(goal_counter : int ref)
      ~(is_exported : string -> bool)
      ~(loc : Asai.Range.t)
      (top : Surface.top)
  : unit
  =
  let m = make_machine ~module_name ~kernel_module ~goal_counter ~is_exported () in
  let g =
    match top with
    | Surface.Universe_decl names -> GTopUniverseDecl names
    | Surface.Let { name; name_loc; bindings; result_ty; body } ->
      GTopLet { loc; name; name_loc; bindings; result_ty; body }
    | Surface.Data _ as d -> GTopData (loc, d)
    | Surface.Stack_def { name; name_loc; params; signature; moves; clauses } ->
      GTopStackDef
        { loc; name; name_loc; bindings = params; result_ty = signature; moves; clauses }
    | Surface.Elim_def
        { name; name_loc; params; signature; opens; intros; target; clauses } ->
      GTopElimDef
        { loc
        ; name
        ; name_loc
        ; bindings = params
        ; result_ty = signature
        ; opens
        ; intros
        ; target
        ; clauses
        }
    | Surface.Operator_decl _ ->
      Reporter.fatalf
        ~loc
        Elab_error
        "internal: Operator_decl reached elaboration (resolver should have consumed it)"
    | Surface.Record _ as r -> GTopRecord (loc, r)
  in
  push m g;
  ignore (drive m);
  if !(m.pending_goals) > 0
  then
    Reporter.emitf
      ~loc
      Goal_unresolved
      "declaration `%s` has %d unresolved goal(s)"
      (name_of_top top)
      !(m.pending_goals)
;;

let check_module
      ?(on_event = fun (_ : Observer.event) -> ())
      ?module_path
      (file : Surface.t)
  : unit
  =
  Observer.run ~on_event
  @@ fun () ->
  let module_path =
    match module_path with
    | Some p -> p
    | None -> [ Filename.chop_extension @@ Filename.basename file.name ]
  in
  let module_name = String.concat "/" module_path in
  let file = Violet_surface.Op_resolver.resolve_module ~module_name file in
  Eio.traceln "checking [module] %s (%s)" module_name file.name;
  let kernel_module = Violet_kernel.Module.create () in
  Context.clear_level_vars ();
  let exports_set =
    let h = Hashtbl.create 16 in
    List.iter (fun (n, _) -> Hashtbl.replace h n ()) file.exports;
    h
  in
  let is_exported name = Hashtbl.mem exports_set name in
  Context.S.section module_path
  @@ fun () ->
  Env.S.section module_path
  @@ fun () ->
  List.iter
    (fun library ->
       (Context.S.modify_visible
        @@ Yuujinchou.Language.(union [ all; renaming library [] ]));
       Env.S.modify_visible @@ Yuujinchou.Language.(union [ all; renaming library [] ]))
    file.imports;
  let goal_counter = ref 0 in
  let run_top (top : Surface.top Asai.Range.located) =
    let loc = Option.get top.loc in
    try
      check_top ~module_name ~kernel_module ~goal_counter ~is_exported ~loc top.value
    with
    | Violet_kernel.Error.Kernel_error err ->
      Kernel_accept.report_rejection ~loc ~name:(name_of_top top.value) err
  in
  List.iter
    (fun top ->
       Reporter.try_with
         ~fatal:(fun diag -> Reporter.emit_diagnostic diag)
         (fun () -> Reporter.merge_loc top.loc (fun () -> run_top top)))
    file.tops;
  let bound_names : (string, unit) Hashtbl.t = Hashtbl.create 16 in
  Yuujinchou.Trie.iter
    (fun path _ ->
       match Bwd.to_list path with
       | [] -> ()
       | seg :: _ -> Hashtbl.replace bound_names seg ())
    (Context.S.get_export ());
  let undefined =
    List.filter (fun (n, _) -> not (Hashtbl.mem bound_names n)) file.exports
  in
  List.iter
    (fun (name, loc) ->
       match loc with
       | Some loc ->
         (match Context.S.resolve [ name ] with
          | Some (ty, _) ->
            let cv = Violet_kernel.Context_view.make ~names:Bwd.Emp ~lvl:0 in
            let pp_ty = Pretty.pp_term cv (Evaluation.quote 0 ty) in
            Observer.emit (Use { path = [ name ]; loc; def_loc = None; ty; pp_ty })
          | None -> ())
       | None -> ())
    file.exports;
  match undefined with
  | [] -> ()
  | names ->
    Reporter.fatalf
      Export_error
      "the following names are listed in \\export but never defined: %s"
      (String.concat ", " (List.map fst names))
;;

let%expect_test "type-directed: bare zero against Nat resolves to Nat/zero" =
  let dummy_loc = Asai.Range.of_lex_range (Lexing.dummy_pos, Lexing.dummy_pos) in
  let loc top = Asai.Range.locate dummy_loc top in
  let nat_data : Surface.top =
    Surface.Data
      { name = "Nat"
      ; name_loc = None
      ; params = []
      ; deps = []
      ; ind_ty = Surface.Universe
      ; ind_ty_loc = None
      ; ctors =
          [ { name = Named "zero"; bound = Surface.Var [ "Nat" ]; implicit = false }
          ; { name = Named "suc"
            ; bound =
                Surface.Pi
                  ( { name = Anon; bound = Surface.Var [ "Nat" ]; implicit = false }
                  , Surface.Var [ "Nat" ] )
            ; implicit = false
            }
          ]
      ; ctor_name_locs = [ None; None ]
      }
  in
  let let_zero : Surface.top =
    Surface.Let
      { name = "x"
      ; name_loc = None
      ; bindings = []
      ; result_ty = Surface.Var [ "Nat" ]
      ; body = Surface.Var [ "zero" ]
      }
  in
  let ast : Surface.t =
    { name = "td-test.vt"
    ; imports = []
    ; exports = []
    ; tops = [ loc nat_data; loc let_zero ]
    }
  in
  with_handlers (fun () -> check_module ast);
  print_endline "ok";
  [%expect
    {|
    +checking [module] td-test (td-test.vt)
    ok
    |}]
;;

let%expect_test "module: \\export-less let stays private from importers" =
  let dummy_loc = Asai.Range.of_lex_range (Lexing.dummy_pos, Lexing.dummy_pos) in
  let loc top = Asai.Range.locate dummy_loc top in
  (* foo : (x : U) -> U => fun x -> x  — well-typed identity on U *)
  let foo_def =
    Surface.Let
      { name = "foo"
      ; name_loc = None
      ; bindings = []
      ; result_ty =
          Surface.Pi
            ( { Syntax.name = Named "x"; bound = Surface.Universe; implicit = false }
            , Surface.Universe )
      ; body =
          Surface.Lambda
            { Syntax.name = Named "x"; bound = Surface.Var [ "x" ]; implicit = false }
      }
  in
  (* uses_foo : (x : U) -> U => foo  — alias for foo; typechecks iff foo is visible *)
  let uses_foo_def =
    Surface.Let
      { name = "uses_foo"
      ; name_loc = None
      ; bindings = []
      ; result_ty =
          Surface.Pi
            ( { Syntax.name = Named "x"; bound = Surface.Universe; implicit = false }
            , Surface.Universe )
      ; body = Surface.Var [ "foo" ]
      }
  in
  let mod_a : Surface.t =
    { name = "a.vt"; imports = []; exports = []; tops = [ loc foo_def ] }
  in
  let mod_b : Surface.t =
    { name = "b.vt"; imports = [ [ "a" ] ]; exports = []; tops = [ loc uses_foo_def ] }
  in
  with_handlers_emitting (fun () ->
    check_module mod_a;
    check_module mod_b);
  [%expect
    {|
    +checking [module] a (a.vt)
    +checking [module] b (b.vt)
    +[Warning] Could not find any data within the subtree at (root).
    +
    +[Warning] Could not find any data within the subtree at a.
    +
    +[Warning] Could not find any data within the subtree at (root).
    +
    +[Warning] Could not find any data within the subtree at a.
    +
    [Reporter.Message.NoVar_error] `foo` is not defined
    |}]
;;

let%expect_test "constructor used in inferred position reports a helpful message" =
  let src =
    "\\universe 𝓤\n\
     \\data Id {A : 𝓤} (x : A) : A -> 𝓤\n\
    \  | refl : Id x x\n\
     \\let f {A : 𝓤} (a : A) : Id a a => refl a\n"
  in
  with_handlers_emitting (fun () ->
    check_module (Violet_surface.Parser.parse_buffer ~filename:"t.vt" src));
  [%expect
    {|
    +checking [module] t (t.vt)
    [Reporter.Message.NoVar_error] `refl` is a constructor of `Id`; it can only be used where its expected type is known (e.g. checked against `Id …`), not as a function head or in an inferred position
    |}]
;;

(* The real-world trigger: a postfix operator whose body is a bare
   constructor (`∎ => refl`). `lower_body` force-applies the hole-free body to
   the operand, so `refl` ends up an application head — an inferred position. *)
let%expect_test "constructor-bodied operator (\\x ∎ => refl) reports helpfully" =
  let src =
    "\\universe 𝓤\n\
     \\data Id {A : 𝓤} (x : A) : A -> 𝓤\n\
    \  | refl : Id x x\n\
     \\operator \"\\x ∎\" => refl\n\
     \\let f {A : 𝓤} (a : A) : Id a a => a ∎\n"
  in
  with_handlers_emitting (fun () ->
    check_module (Violet_surface.Parser.parse_buffer ~filename:"t.vt" src));
  [%expect
    {|
    +checking [module] t (t.vt)
    [Reporter.Message.NoVar_error] `refl` is a constructor of `Id`; it can only be used where its expected type is known (e.g. checked against `Id …`), not as a function head or in an inferred position
    |}]
;;

(* Regression guard: a constructor used correctly (checking position) must
   still resolve type-directed and NOT trip the new diagnostic. *)
let%expect_test "constructor in checking position still resolves" =
  let src =
    "\\universe 𝓤\n\
     \\data Id {A : 𝓤} (x : A) : A -> 𝓤\n\
    \  | refl : Id x x\n\
     \\let f {A : 𝓤} (a : A) : Id a a => refl\n"
  in
  with_handlers_emitting (fun () ->
    check_module (Violet_surface.Parser.parse_buffer ~filename:"t.vt" src));
  [%expect {| +checking [module] t (t.vt) |}]
;;

(* A name that is neither a binding nor a constructor still gets the plain
   "is not defined" message — the new branch must not swallow that case. *)
let%expect_test "genuinely unbound name still says is not defined" =
  let src = "\\universe 𝓤\n\\let f : 𝓤 => bogus\n" in
  with_handlers_emitting (fun () ->
    check_module (Violet_surface.Parser.parse_buffer ~filename:"t.vt" src));
  [%expect
    {|
    +checking [module] t (t.vt)
    [Reporter.Message.NoVar_error] `bogus` is not defined
    |}]
;;

(* When several inductives share a constructor name, the message lists them
   all (and still cannot disambiguate without an expected type). *)
let%expect_test "constructor shared by two inductives lists both owners" =
  let src =
    "\\universe 𝓤\n\
     \\data A : 𝓤\n\
    \  | mk : A\n\
     \\data B : 𝓤\n\
    \  | mk : B\n\
     \\let f : A => mk mk\n"
  in
  with_handlers_emitting (fun () ->
    check_module (Violet_surface.Parser.parse_buffer ~filename:"t.vt" src));
  [%expect
    {|
    +checking [module] t (t.vt)
    [Reporter.Message.NoVar_error] `mk` is a constructor of `A`, `B`; it can only be used where its expected type is known (e.g. checked against `A …`), not as a function head or in an inferred position
    |}]
;;

let%expect_test "module: \\export-listed let is visible to importers" =
  let dummy_loc = Asai.Range.of_lex_range (Lexing.dummy_pos, Lexing.dummy_pos) in
  let loc top = Asai.Range.locate dummy_loc top in
  (* foo : (x : U) -> U => fun x -> x  — well-typed identity on U *)
  let foo_def =
    Surface.Let
      { name = "foo"
      ; name_loc = None
      ; bindings = []
      ; result_ty =
          Surface.Pi
            ( { Syntax.name = Named "x"; bound = Surface.Universe; implicit = false }
            , Surface.Universe )
      ; body =
          Surface.Lambda
            { Syntax.name = Named "x"; bound = Surface.Var [ "x" ]; implicit = false }
      }
  in
  (* uses_foo : (x : U) -> U => foo  — alias for foo; typechecks iff foo is visible *)
  let uses_foo_def =
    Surface.Let
      { name = "uses_foo"
      ; name_loc = None
      ; bindings = []
      ; result_ty =
          Surface.Pi
            ( { Syntax.name = Named "x"; bound = Surface.Universe; implicit = false }
            , Surface.Universe )
      ; body = Surface.Var [ "foo" ]
      }
  in
  let mod_a : Surface.t =
    { name = "a.vt"; imports = []; exports = [ "foo", None ]; tops = [ loc foo_def ] }
  in
  let mod_b : Surface.t =
    { name = "b.vt"; imports = [ [ "a" ] ]; exports = []; tops = [ loc uses_foo_def ] }
  in
  with_handlers (fun () ->
    check_module mod_a;
    check_module mod_b);
  print_endline "ok";
  [%expect
    {|
    +checking [module] a (a.vt)
    +checking [module] b (b.vt)
    ok
    |}]
;;

let%expect_test "module: \\export of an undefined name fails" =
  let mod_a : Surface.t =
    { name = "a.vt"; imports = []; exports = [ "ghost", None ]; tops = [] }
  in
  (try
     with_handlers (fun () -> check_module mod_a);
     print_endline "UNEXPECTED: undefined export accepted"
   with
   | _ -> print_endline "rejected as expected");
  [%expect
    {|
    +checking [module] a (a.vt)
    rejected as expected
    |}]
;;

let%expect_test
    "module: \\export of an inductive bundle: Nat, ctors, elim visible cross-module"
  =
  let dummy_loc = Asai.Range.of_lex_range (Lexing.dummy_pos, Lexing.dummy_pos) in
  let loc top = Asai.Range.locate dummy_loc top in
  let nat_data : Surface.top =
    Surface.Data
      { name = "Nat"
      ; name_loc = None
      ; params = []
      ; deps = []
      ; ind_ty = Surface.Universe
      ; ind_ty_loc = None
      ; ctors =
          [ { name = Named "zero"; bound = Surface.Var [ "Nat" ]; implicit = false }
          ; { name = Named "suc"
            ; bound =
                Surface.Pi
                  ( { name = Anon; bound = Surface.Var [ "Nat" ]; implicit = false }
                  , Surface.Var [ "Nat" ] )
            ; implicit = false
            }
          ]
      ; ctor_name_locs = [ None; None ]
      }
  in
  let mod_a : Surface.t =
    { name = "a.vt"; imports = []; exports = [ "Nat", None ]; tops = [ loc nat_data ] }
  in
  (* uses_bundle : Nat => Nat/zero — references both the type and a constructor,
     proving the inductive bundle (type + ctors) is visible cross-module. *)
  let mod_b : Surface.t =
    { name = "b.vt"
    ; imports = [ [ "a" ] ]
    ; exports = []
    ; tops =
        [ loc
            (Surface.Let
               { name = "uses_bundle"
               ; name_loc = None
               ; bindings = []
               ; result_ty = Surface.Var [ "Nat" ]
               ; body = Surface.Var [ "Nat"; "zero" ]
               })
        ]
    }
  in
  with_handlers (fun () ->
    check_module mod_a;
    check_module mod_b);
  print_endline "ok";
  [%expect
    {|
    +checking [module] a (a.vt)
    +checking [module] b (b.vt)
    ok
    |}]
;;

let%expect_test
    "module: \\export of a record bundle: Point companions visible cross-module"
  =
  let dummy_loc = Asai.Range.of_lex_range (Lexing.dummy_pos, Lexing.dummy_pos) in
  let loc top = Asai.Range.locate dummy_loc top in
  let nat_data : Surface.top =
    Surface.Data
      { name = "Nat"
      ; name_loc = None
      ; params = []
      ; deps = []
      ; ind_ty = Surface.Universe
      ; ind_ty_loc = None
      ; ctors =
          [ { name = Named "zero"; bound = Surface.Var [ "Nat" ]; implicit = false }
          ; { name = Named "suc"
            ; bound =
                Surface.Pi
                  ( { name = Anon; bound = Surface.Var [ "Nat" ]; implicit = false }
                  , Surface.Var [ "Nat" ] )
            ; implicit = false
            }
          ]
      ; ctor_name_locs = [ None; None ]
      }
  in
  let point_record : Surface.top =
    Surface.Record
      { name = "Point"
      ; name_loc = None
      ; params = []
      ; ind_ty = Surface.Universe
      ; fields =
          [ { name = Named "x"; bound = Surface.Var [ "Nat" ]; implicit = false }
          ; { name = Named "y"; bound = Surface.Var [ "Nat" ]; implicit = false }
          ]
      }
  in
  (* Module A: defines Nat + Point, exports only "Point" (which should cluster
     all five companions: Point, Point/mk, Point/x, Point/y, Point/elim). *)
  let mod_a : Surface.t =
    { name = "a.vt"
    ; imports = []
    ; exports = [ "Nat", None; "Point", None ]
    ; tops = [ loc nat_data; loc point_record ]
    }
  in
  (* Module B: imports a, uses Point/x — proves the companion is cross-module visible.
     Note: field projectors are published under the flat name "Point/x" (single segment),
     mirroring how the env stores them, so we resolve via Var ["Point/x"]. *)
  let mod_b : Surface.t =
    { name = "b.vt"
    ; imports = [ [ "a" ] ]
    ; exports = []
    ; tops =
        [ loc
            (Surface.Let
               { name = "uses_proj"
               ; name_loc = None
               ; bindings = []
               ; result_ty =
                   Surface.Pi
                     ( { name = Anon; bound = Surface.Var [ "Point" ]; implicit = false }
                     , Surface.Var [ "Nat" ] )
               ; body = Surface.Var [ "Point/x" ]
               })
        ]
    }
  in
  with_handlers (fun () ->
    check_module mod_a;
    check_module mod_b);
  print_endline "ok";
  [%expect
    {|
    +checking [module] a (a.vt)
    +checking [module] b (b.vt)
    ok
    |}]
;;

let%expect_test "record: \\record Point : U | x : Nat | y : Nat produces 5 Module entries"
  =
  let dummy_loc = Asai.Range.of_lex_range (Lexing.dummy_pos, Lexing.dummy_pos) in
  (* First declare Nat so fields can refer to it *)
  let nat_data : Surface.top =
    Surface.Data
      { name = "Nat"
      ; name_loc = None
      ; params = []
      ; deps = []
      ; ind_ty = Surface.Universe
      ; ind_ty_loc = None
      ; ctors =
          [ { name = Named "zero"; bound = Surface.Var [ "Nat" ]; implicit = false }
          ; { name = Named "suc"
            ; bound =
                Surface.Pi
                  ( { name = Anon; bound = Surface.Var [ "Nat" ]; implicit = false }
                  , Surface.Var [ "Nat" ] )
            ; implicit = false
            }
          ]
      ; ctor_name_locs = [ None; None ]
      }
  in
  let point_record : Surface.top =
    Surface.Record
      { name = "Point"
      ; name_loc = None
      ; params = []
      ; ind_ty = Surface.Universe
      ; fields =
          [ { name = Named "x"; bound = Surface.Var [ "Nat" ]; implicit = false }
          ; { name = Named "y"; bound = Surface.Var [ "Nat" ]; implicit = false }
          ]
      }
  in
  let kernel_module = Violet_kernel.Module.create () in
  with_handlers (fun () ->
    let goal_counter = ref 0 in
    let is_exported _ = false in
    Context.clear_level_vars ();
    Context.declare_level_var "U";
    check_top
      ~module_name:"test"
      ~kernel_module
      ~goal_counter
      ~is_exported
      ~loc:dummy_loc
      nat_data;
    check_top
      ~module_name:"test"
      ~kernel_module
      ~goal_counter
      ~is_exported
      ~loc:dummy_loc
      point_record);
  (* Verify the 5 expected entries are present in the kernel module *)
  let present name =
    match Violet_kernel.Module.lookup kernel_module ("test." ^ name) with
    | Some _ -> true
    | None -> false
  in
  let entries = [ "Point"; "Point/mk"; "Point/x"; "Point/y"; "Point/elim" ] in
  List.iter
    (fun name ->
       Printf.printf "%s: %s\n" name (if present name then "present" else "MISSING"))
    entries;
  [%expect
    {|
    Point: present
    Point/mk: present
    Point/x: present
    Point/y: present
    Point/elim: present
    |}]
;;

let%expect_test "check-mode record literal elaboration produces RecordIntro" =
  (* Set up: Nat data + Pair record + a let that uses a record literal.
     Verifies that { fst = Nat/zero, snd = Nat/zero } : Pair Nat Nat
     elaborates to RecordIntro { name = "Pair"; fields = [("fst", ...); ("snd", ...)] }.
  *)
  let dummy_loc = Asai.Range.of_lex_range (Lexing.dummy_pos, Lexing.dummy_pos) in
  let nat_data : Surface.top =
    Surface.Data
      { name = "Nat"
      ; name_loc = None
      ; params = []
      ; deps = []
      ; ind_ty = Surface.Universe
      ; ind_ty_loc = None
      ; ctors =
          [ { name = Named "zero"; bound = Surface.Var [ "Nat" ]; implicit = false }
          ; { name = Named "suc"
            ; bound =
                Surface.Pi
                  ( { name = Anon; bound = Surface.Var [ "Nat" ]; implicit = false }
                  , Surface.Var [ "Nat" ] )
            ; implicit = false
            }
          ]
      ; ctor_name_locs = [ None; None ]
      }
  in
  let pair_record : Surface.top =
    Surface.Record
      { name = "Pair"
      ; name_loc = None
      ; params =
          [ { name = Named "A"; bound = Surface.Universe; implicit = false }
          ; { name = Named "B"; bound = Surface.Universe; implicit = false }
          ]
      ; ind_ty = Surface.Universe
      ; fields =
          [ { name = Named "fst"; bound = Surface.Var [ "A" ]; implicit = false }
          ; { name = Named "snd"; bound = Surface.Var [ "B" ]; implicit = false }
          ]
      }
  in
  (* \let p : Pair Nat Nat => { fst = Nat/zero, snd = Nat/zero } *)
  let p_let : Surface.top =
    Surface.Let
      { name = "p"
      ; name_loc = None
      ; bindings = []
      ; result_ty =
          Surface.App
            ( false
            , Surface.App (false, Surface.Var [ "Pair" ], Surface.Var [ "Nat" ])
            , Surface.Var [ "Nat" ] )
      ; body =
          Surface.RecordLit
            [ "fst", Surface.Var [ "Nat"; "zero" ]; "snd", Surface.Var [ "Nat"; "zero" ] ]
      }
  in
  let kernel_module = Violet_kernel.Module.create () in
  with_handlers (fun () ->
    let goal_counter = ref 0 in
    let is_exported _ = false in
    Context.clear_level_vars ();
    Context.declare_level_var "U";
    check_top
      ~module_name:"test"
      ~kernel_module
      ~goal_counter
      ~is_exported
      ~loc:dummy_loc
      nat_data;
    check_top
      ~module_name:"test"
      ~kernel_module
      ~goal_counter
      ~is_exported
      ~loc:dummy_loc
      pair_record;
    check_top
      ~module_name:"test"
      ~kernel_module
      ~goal_counter
      ~is_exported
      ~loc:dummy_loc
      p_let);
  (match Violet_kernel.Module.lookup kernel_module "test.p" with
   | Some (Violet_kernel.Module.Let { body; _ }) ->
     Printf.printf "body: %s\n" ([%show: Core.term] body)
   | _ -> Printf.printf "not found or wrong decl kind\n");
  [%expect {| body: Pair{ fst = Nat/zero, snd = Nat/zero } |}]
;;

let%expect_test "check-mode record literal with missing field gives error" =
  let dummy_loc = Asai.Range.of_lex_range (Lexing.dummy_pos, Lexing.dummy_pos) in
  let nat_data : Surface.top =
    Surface.Data
      { name = "Nat"
      ; name_loc = None
      ; params = []
      ; deps = []
      ; ind_ty = Surface.Universe
      ; ind_ty_loc = None
      ; ctors =
          [ { name = Named "zero"; bound = Surface.Var [ "Nat" ]; implicit = false }
          ; { name = Named "suc"
            ; bound =
                Surface.Pi
                  ( { name = Anon; bound = Surface.Var [ "Nat" ]; implicit = false }
                  , Surface.Var [ "Nat" ] )
            ; implicit = false
            }
          ]
      ; ctor_name_locs = [ None; None ]
      }
  in
  let pair_record : Surface.top =
    Surface.Record
      { name = "Pair"
      ; name_loc = None
      ; params =
          [ { name = Named "A"; bound = Surface.Universe; implicit = false }
          ; { name = Named "B"; bound = Surface.Universe; implicit = false }
          ]
      ; ind_ty = Surface.Universe
      ; fields =
          [ { name = Named "fst"; bound = Surface.Var [ "A" ]; implicit = false }
          ; { name = Named "snd"; bound = Surface.Var [ "B" ]; implicit = false }
          ]
      }
  in
  (* \let p : Pair Nat Nat => { fst = Nat/zero }  -- missing snd *)
  let p_let : Surface.top =
    Surface.Let
      { name = "p"
      ; name_loc = None
      ; bindings = []
      ; result_ty =
          Surface.App
            ( false
            , Surface.App (false, Surface.Var [ "Pair" ], Surface.Var [ "Nat" ])
            , Surface.Var [ "Nat" ] )
      ; body = Surface.RecordLit [ "fst", Surface.Var [ "Nat"; "zero" ] ]
      }
  in
  let kernel_module = Violet_kernel.Module.create () in
  let result =
    try
      with_handlers (fun () ->
        let goal_counter = ref 0 in
        let is_exported _ = false in
        Context.clear_level_vars ();
        Context.declare_level_var "U";
        check_top
          ~module_name:"test"
          ~kernel_module
          ~goal_counter
          ~is_exported
          ~loc:dummy_loc
          nat_data;
        check_top
          ~module_name:"test"
          ~kernel_module
          ~goal_counter
          ~is_exported
          ~loc:dummy_loc
          pair_record;
        check_top
          ~module_name:"test"
          ~kernel_module
          ~goal_counter
          ~is_exported
          ~loc:dummy_loc
          p_let);
      "no error"
    with
    | Failure msg -> "error: " ^ msg
  in
  Printf.printf "%s\n" result;
  [%expect {| error: Reporter.Message.Elab_error |}]
;;
