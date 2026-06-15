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
    when match term.Surface.node with
         | Lambda { implicit = true; _ } -> false
         | _ -> true ->
    let body_ty = b (Core.RigidLocal (m.ctx.lvl, Bwd.Emp)) in
    save_ctx m;
    m.ctx <- bind m.ctx { Surface.loc; value = pi_name } a;
    push m (KLam_Body (loc, pi_name, true));
    push m (GCheck (term, body_ty));
    true
  | _ -> false
;;

let rec dispatch (m : machine) (g : goal) : unit =
  match g with
  | GCheck (term, ty) when try_insert_implicit_abstraction m term.loc term ty -> ()
  | GInfer { node = Universe; _ } ->
    m.result
    <- Some
         (PTermType (Core.Universe Level.LZero, Core.Universe (Level.LSuc Level.LZero)))
  | GInfer { loc; node = Var [ x ] } ->
    (match resolve_local m.ctx x with
     | Some i ->
       let ty = local_type m.ctx i in
       let def_loc = Some (local_binder_loc m.ctx i) in
       let pp_ty = Notation.pp_term (view_of_ctx m.ctx) (Evaluation.quote m.ctx.lvl ty) in
       Observer.emit (Use { path = [ x ]; loc; def_loc; ty; pp_ty });
       m.result <- Some (PTermType (Core.LocalVar i, ty))
     | None ->
       (match resolve_universe_var x with
        | Some l ->
          let ty = Core.Universe (Level.lsuc l) in
          let pp_ty =
            Notation.pp_term (view_of_ctx m.ctx) (Evaluation.quote m.ctx.lvl ty)
          in
          Observer.emit (Use { path = [ x ]; loc; def_loc = None; ty; pp_ty });
          m.result <- Some (PTermType (Core.Universe l, ty))
        | None ->
          let ty = Context.lookup x in
          let pp_ty =
            Notation.pp_term (view_of_ctx m.ctx) (Evaluation.quote m.ctx.lvl ty)
          in
          Observer.emit (Use { path = [ x ]; loc; def_loc = None; ty; pp_ty });
          m.result <- Some (PTermType (Core.Var x, ty))))
  | GInfer { loc; node = Var path } ->
    let ty = Context.lookup_path path in
    let joined = Syntax.Name.of_segments path in
    let pp_ty = Notation.pp_term (view_of_ctx m.ctx) (Evaluation.quote m.ctx.lvl ty) in
    Observer.emit (Use { path; loc; def_loc = None; ty; pp_ty });
    m.result <- Some (PTermType (Core.Var joined, ty))
  | GInferType { loc; node = Goal name_opt } ->
    let name = resolve_goal_name m name_opt in
    emit_goal_report ~loc m ~name ~target:(Core.Universe Level.LZero);
    incr m.pending_goals;
    m.result <- Some (PType (Meta.fresh_goal m.ctx.lvl, Level.LZero))
  | GInferType ({ loc; _ } as p) ->
    push m (KEnsureUniverse loc);
    push m (GInfer p)
  | KEnsureUniverse loc ->
    (match take_result m with
     | PTermType (tm, ty) ->
       (match Evaluation.force_head ty with
        | Core.Universe l -> m.result <- Some (PType (tm, l))
        | _ ->
          Reporter.fatalf
            ~loc
            Type_error
            "expected a type, but got `%s : %s`"
            (Notation.pp_term (view_of_ctx m.ctx) tm)
            (Notation.pp_term (view_of_ctx m.ctx) (Evaluation.quote m.ctx.lvl ty)))
     | other ->
       Reporter.fatalf Elab_error "KEnsureUniverse: bad result %s" (produced_tag other))
  | GInfer { loc; node = Pi ({ name; bound = a; implicit }, b) } ->
    push m (KPi_HaveDom (loc, name, implicit, b));
    push m (GInferType a)
  | KPi_HaveDom (loc, name, implicit, body) ->
    (match take_result m with
     | PType (a_tm, l_a) ->
       let a_val = Evaluation.eval m.ctx.env a_tm in
       (match name.Surface.value with
        | Named n ->
          let pp_ty = Notation.pp_term (view_of_ctx m.ctx) a_tm in
          Observer.emit
            (Binder
               { path = [ n ]
               ; loc = name.Surface.loc
               ; ty = Some a_val
               ; pp_ty = Some pp_ty
               })
        | Anon -> ());
       save_ctx m;
       m.ctx <- bind m.ctx name a_val;
       push m (KPi_HaveCod (loc, name.Surface.value, implicit, a_tm, l_a));
       push m (GInferType body)
     | other ->
       Reporter.fatalf Elab_error "KPi_HaveDom: bad result %s" (produced_tag other))
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
       Reporter.fatalf Elab_error "KPi_HaveCod: bad result %s" (produced_tag other))
  | GCheck ({ loc; node = Lambda { name; bound = body; implicit = lambda_mode } }, ty) ->
    (match Evaluation.force_head ty with
     | Core.VPi ({ name = _; bound = a; implicit = pi_mode }, b) ->
       if lambda_mode <> pi_mode
       then Reporter.fatalf ~loc Elab_error "mode mismatching"
       else begin
         (match name.Surface.value with
          | Named n ->
            let pp_ty =
              Notation.pp_term (view_of_ctx m.ctx) (Evaluation.quote m.ctx.lvl a)
            in
            Observer.emit
              (Binder
                 { path = [ n ]; loc = name.Surface.loc; ty = Some a; pp_ty = Some pp_ty })
          | Anon -> ());
         let body_ty = b (Core.RigidLocal (m.ctx.lvl, Bwd.Emp)) in
         save_ctx m;
         m.ctx <- bind m.ctx name a;
         push m (KLam_Body (loc, name.Surface.value, lambda_mode));
         push m (GCheck (body, body_ty))
       end
     | _ ->
       let ty = Notation.pp_term (view_of_ctx m.ctx) (Evaluation.quote m.ctx.lvl ty) in
       Reporter.fatalf ~loc Elab_error "Lambda checked against non-Pi: %s" ty)
  | KLam_Body (_loc, name, implicit) ->
    (match take_result m with
     | PTerm body_tm ->
       restore_ctx m;
       m.result <- Some (PTerm (Core.Lambda { name; bound = body_tm; implicit }))
     | other -> Reporter.fatalf Elab_error "KLam_Body: bad result %s" (produced_tag other))
  | GInfer { loc; node = TypedLambda ({ name; bound = ty; implicit }, body) } ->
    push m (KTypedLam_HaveDom (loc, name, implicit, body));
    push m (GInferType ty)
  | KTypedLam_HaveDom (loc, name, implicit, body) ->
    (match take_result m with
     | PType (ty_tm, _) ->
       let ty_val = Evaluation.eval m.ctx.env ty_tm in
       (match name.Surface.value with
        | Named n ->
          let pp_ty = Notation.pp_term (view_of_ctx m.ctx) ty_tm in
          Observer.emit
            (Binder
               { path = [ n ]
               ; loc = name.Surface.loc
               ; ty = Some ty_val
               ; pp_ty = Some pp_ty
               })
        | Anon -> ());
       save_ctx m;
       m.ctx <- bind m.ctx name ty_val;
       push m (KTypedLam_HaveBody (loc, name.Surface.value, implicit, ty_tm, ty_val));
       push m (GInfer body)
     | other ->
       Reporter.fatalf Elab_error "KTypedLam_HaveDom: bad result %s" (produced_tag other))
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
       Reporter.fatalf Elab_error "KTypedLam_HaveBody: bad result %s" (produced_tag other))
  | GInfer { loc; node = App (is_implicit, f, arg) } ->
    push m (KApp_HaveFn (loc, is_implicit, arg));
    push m (GInfer f)
  | KApp_HaveFn (loc, is_implicit, arg) ->
    (match take_result m with
     | PTermType (f_tm, f_ty) ->
       (match Evaluation.force_head f_ty with
        | Core.VPi ({ implicit; name = pi_name; bound = a }, b) ->
          if is_implicit = implicit
          then begin
            push m (KApp_HaveArg (loc, f_tm, b, implicit));
            push m (GCheck (arg, a))
          end
          else if implicit
          then begin
            (* Insert a fresh implicit meta on the f side, then retry. *)
            let display =
              Printf.sprintf
                "{%s : %s}"
                (Syntax.Name.to_string pi_name)
                (Notation.pp_term (view_of_ctx m.ctx) (Evaluation.quote m.ctx.lvl a))
            in
            let meta_tm = Meta.meta_fresh_with m.ctx.lvl ~origin:{ loc; display } in
            let meta_val = Evaluation.eval m.ctx.env meta_tm in
            let new_f_tm = Core.App (f_tm, meta_tm, true) in
            let new_f_ty = b meta_val in
            m.result <- Some (PTermType (new_f_tm, new_f_ty));
            push m (KApp_HaveFn (loc, is_implicit, arg))
          end
          else
            Reporter.fatalf
              ~loc
              Elab_error
              "Bad apply at %s"
              (Notation.pp_term (view_of_ctx m.ctx) f_tm)
        | _ ->
          let ty =
            Notation.pp_term (view_of_ctx m.ctx) (Evaluation.quote m.ctx.lvl f_ty)
          in
          Reporter.fatalf
            ~loc
            Type_error
            "cannot apply to `(%s) : %s`"
            (Notation.pp_term (view_of_ctx m.ctx) f_tm)
            ty)
     | other ->
       Reporter.fatalf Elab_error "KApp_HaveFn: bad result %s" (produced_tag other))
  | KApp_HaveArg (_loc, f_tm, b, implicit) ->
    (match take_result m with
     | PTerm arg_tm ->
       let arg_val = Evaluation.eval m.ctx.env arg_tm in
       m.result <- Some (PTermType (Core.App (f_tm, arg_tm, implicit), b arg_val))
     | other ->
       Reporter.fatalf Elab_error "KApp_HaveArg: bad result %s" (produced_tag other))
  | GInfer { loc; node = Op_soup _ } | GCheck ({ loc; node = Op_soup _ }, _) ->
    Reporter.fatalf
      ~loc
      Elab_error
      "internal: Op_soup reached elaborator (resolver should have lowered it)"
  | GInfer { loc; node = RecordLit _ } -> Elab_record.handle_infer_record_lit m loc
  | GCheck ({ loc; node = RecordLit entries }, expected_ty) ->
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
  | GInfer { loc; node = RecordUpdate _ } -> Elab_record.handle_infer_record_update m loc
  | GCheck ({ loc; node = RecordUpdate (base, overrides) }, expected_ty) ->
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
  | GInfer { loc; node = Proj (e, f) } -> Elab_record.handle_infer_proj m loc e f
  | KProj_HaveRec (loc, f) -> Elab_record.handle_proj_have_rec m loc f
  | GInfer { loc; node = Lambda _ } ->
    Reporter.fatalf ~loc Elab_error "cannot infer lambda term"
  | GCheck ({ node = Hole; _ }, _) -> m.result <- Some (PTerm (Meta.meta_fresh m.ctx.lvl))
  | GInfer { node = Hole; _ } ->
    let ty = Evaluation.eval m.ctx.env (Meta.meta_fresh m.ctx.lvl) in
    let tm = Meta.meta_fresh m.ctx.lvl in
    m.result <- Some (PTermType (tm, ty))
  | GCheck ({ loc; node = Inline_elim d }, ty) ->
    Elab_elim.handle_check_inline_elim ~infer_term m loc d ty
  | GInfer { loc; node = Inline_elim _ } ->
    Reporter.fatalf ~loc Elab_error "cannot infer the type of a nested `<= \\elim`"
  | GCheck ({ loc; node = Goal name_opt }, ty) ->
    let name = resolve_goal_name m name_opt in
    emit_goal_report ~loc m ~name ~target:ty;
    incr m.pending_goals;
    m.result <- Some (PTerm (Meta.fresh_goal m.ctx.lvl))
  | GInfer { loc; node = Goal name_opt } ->
    let name = resolve_goal_name m name_opt in
    let ty_tm = Meta.fresh_goal m.ctx.lvl in
    let ty_val = Evaluation.eval m.ctx.env ty_tm in
    emit_goal_report ~loc m ~name ~target:ty_val;
    incr m.pending_goals;
    m.result <- Some (PTermType (Meta.fresh_goal m.ctx.lvl, ty_val))
  | GInfer { loc; node = Max (a, b) } ->
    push m (KMax_HaveLeft (loc, b));
    push m (GInfer a)
  | KMax_HaveLeft (loc, b) ->
    (match take_result m with
     | PTermType (Core.Universe l_a, _) ->
       push m (KMax_HaveRight (loc, l_a));
       push m (GInfer b)
     | PTermType (other_tm, _) ->
       Reporter.fatalf
         ~loc
         Type_error
         "operands of `⊔` must be universes, got `%s`"
         (Notation.pp_term (view_of_ctx m.ctx) other_tm)
     | other ->
       Reporter.fatalf Elab_error "KMax_HaveLeft: bad result %s" (produced_tag other))
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
         (Notation.pp_term (view_of_ctx m.ctx) other_tm)
     | other ->
       Reporter.fatalf Elab_error "KMax_HaveRight: bad result %s" (produced_tag other))
  | GInfer { loc; node = IdAbsurd p } ->
    push m (KIdAbsurd_HaveArg loc);
    push m (GInfer p)
  | GInfer { loc; node = Absurd p } ->
    push m (KAbsurd_HaveArg loc);
    push m (GCheck (p, Core.VEmpty))
  | KAbsurd_HaveArg loc ->
    (match take_result m with
     | PTermType (p_tm, _) | PTerm p_tm ->
       let ret_ty =
         Meta.fresh_meta_value_with m.ctx.lvl ~origin:{ loc; display = "absurd" }
       in
       m.result <- Some (PTermType (Core.Absurd p_tm, ret_ty))
     | other ->
       Reporter.fatalf Elab_error "KAbsurd_HaveArg: bad result %s" (produced_tag other))
  | KIdAbsurd_HaveArg loc ->
    (match take_result m with
     | PTermType (p_tm, p_ty) ->
       (* Verify p_ty is `Id <A> <c1 args> <c2 args>` with c1 ≠ c2 (same
          inductive, i.e. constructors of the underlying `A`). The spine
          shape is set by the Id data declaration; we read positions 1 and
          2 of the spine for the two Id arguments. *)
       (match Evaluation.force_head p_ty with
        | Core.IndType (ind_name, spine) when String.equal ind_name "Id" ->
          let xs = Bwd.to_list (Core.spine_values spine) in
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
             let empty_ty = Core.VEmpty in
             m.result <- Some (PTermType (Core.IdAbsurd p_tm, empty_ty))
           | l, r ->
             Reporter.fatalf
               ~loc
               Elab_error
               "\\absurd-id: expected Id of distinct-ctor-headed values, got `Id _ %s %s`"
               (Notation.pp_term (view_of_ctx m.ctx) (Evaluation.quote m.ctx.lvl l))
               (Notation.pp_term (view_of_ctx m.ctx) (Evaluation.quote m.ctx.lvl r)))
        | other ->
          Reporter.fatalf
            ~loc
            Elab_error
            "\\absurd-id: argument is not Id-typed, got `%s`"
            (Notation.pp_term (view_of_ctx m.ctx) (Evaluation.quote m.ctx.lvl other)))
     | other ->
       Reporter.fatalf Elab_error "KIdAbsurd_HaveArg: bad result %s" (produced_tag other))
  | GCheck (({ loc; node = Var [ x ] } as term), expected)
    when Option.is_none (resolve_local m.ctx x) ->
    (* Type-directed resolution: if expected forces to IndType(ind, _) and
       [ind; x] is bound in Context, use the namespaced binding.
       Otherwise fall through to standard inference. *)
    let head = Evaluation.force_head expected in
    (match head with
     | Core.IndType (ind, _) when Context.has_path [ ind; x ] ->
       (* Build the namespaced term: kernel eval resolves "ind/x" via E.lookup *)
       let ty = Context.lookup_path [ ind; x ] in
       let tm : Core.term = Core.Var (Syntax.Name.qualify ind x) in
       push m (KCheckBy_Infer (loc, expected));
       m.result <- Some (PTermType (tm, ty))
     | _ ->
       push m (KCheckBy_Infer (loc, expected));
       push m (GInfer term))
  | GCheck (other, expected) ->
    push m (KCheckBy_Infer (other.loc, expected));
    push m (GInfer other)
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
               (Notation.pp_term (view_of_ctx m.ctx) (Evaluation.quote m.ctx.lvl a))
           in
           let meta_tm = Meta.meta_fresh_with m.ctx.lvl ~origin:{ loc; display } in
           let meta_val = Evaluation.eval m.ctx.env meta_tm in
           insert_implicit_apps (Core.App (tm, meta_tm, true)) (b meta_val)
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
       Reporter.fatalf Elab_error "KCheckBy_Infer: bad result %s" (produced_tag other))
  | GTopUniverseDecl names -> Elab_decl.handle_universe_decl m names
  | GTopLet { loc; name; bindings; result_ty; body } ->
    Elab_decl.handle_top_let m ~loc ~name ~bindings ~result_ty ~body
  | KTopLet_HaveType { loc; name; body; bindings } ->
    Elab_decl.handle_top_let_have_type m ~loc ~name ~body ~bindings
  | KTopLet_HaveBody { loc; name; typ_tm; typ_val } ->
    Elab_decl.handle_top_let_have_body m ~loc ~name ~typ_tm ~typ_val
  | GTopAxiom { loc; name; bindings; result_ty } ->
    Elab_decl.handle_top_axiom m ~loc ~name ~bindings ~result_ty
  | KTopAxiom_HaveType { loc; name } -> Elab_decl.handle_top_axiom_have_type m ~loc ~name
  | KTopElimDef_HaveBody { loc; name; typ_tm; typ_val; func_name; target_pos } ->
    Elab_elim.handle_elim_def_have_body
      m
      ~loc
      ~name
      ~typ_tm
      ~typ_val
      ~func_name
      ~target_pos
  | GTopStackDef { loc; name; bindings; result_ty; moves; clauses } ->
    Elab_elim.handle_stack_def m ~loc ~name ~bindings ~result_ty ~moves ~clauses
  | KTopStackDef_HaveType { loc; name; bindings; signature; moves; clauses } ->
    Elab_elim.handle_stack_def_have_type m ~loc ~name ~bindings ~signature ~moves ~clauses
  | GTopElimDef { loc; name; bindings; result_ty; opens; intros; target; clauses } ->
    Elab_elim.handle_elim_def
      m
      ~loc
      ~name
      ~bindings
      ~result_ty
      ~opens
      ~intros
      ~target
      ~clauses
  | KTopElimDef_HaveType
      { loc; name; bindings; signature; opens; intros; target; clauses } ->
    Elab_elim.handle_elim_def_have_type
      m
      ~loc
      ~name
      ~bindings
      ~signature
      ~opens
      ~intros
      ~target
      ~clauses
  | GTopData (loc, data) -> Elab_data.handle_top_data m loc data
  | KTopData_HaveType { loc; name; params; deps; ind_ty; ctors } ->
    Elab_data.handle_top_data_have_type
      ~check_type
      m
      ~loc
      ~name
      ~params
      ~deps
      ~ind_ty
      ~ctors
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

and infer_type (ctx : local_ctx) (pretype : Surface.pretype) : Core.term * Level.level =
  let m =
    make_machine
      ~module_name:"_internal"
      ~kernel_module:(Violet_kernel.Module.create ())
      ~goal_counter:(ref 0)
      ~is_exported:(fun _ -> false)
      ()
  in
  m.ctx <- ctx;
  push m (GInferType pretype);
  match drive m with
  | PType (tm, l) -> tm, l
  | other ->
    Reporter.fatalf
      ~loc:pretype.Surface.loc
      Elab_error
      "infer_type: %s"
      (produced_tag other)

and check_type (ctx : local_ctx) (pretype : Surface.pretype) : Core.term =
  fst (infer_type ctx pretype)

and infer_term (ctx : local_ctx) (term : Surface.preterm) : Core.term * Core.value =
  let m =
    make_machine
      ~module_name:"_internal"
      ~kernel_module:(Violet_kernel.Module.create ())
      ~goal_counter:(ref 0)
      ~is_exported:(fun _ -> false)
      ()
  in
  m.ctx <- ctx;
  push m (GInfer term);
  match drive m with
  | PTermType (tm, ty) -> tm, ty
  | other ->
    Reporter.fatalf ~loc:term.Surface.loc Elab_error "infer_term: %s" (produced_tag other)
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

let dloc = Surface.dummy_loc
let d = Surface.Mk.d
let dn = Surface.Mk.dn

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
  push m (GInfer p);
  match drive m with
  | PTermType (tm, ty) -> tm, ty
  | other -> Reporter.fatalf Elab_error "infer_for_test: got %s" (produced_tag other)
;;

let%expect_test "infer Universe" =
  let tm, ty = infer_for_test (d Surface.Universe) in
  Printf.printf
    "%s : %s"
    (Notation.pp_term Context_view.empty tm)
    (Notation.pp_term Context_view.empty (Evaluation.quote 0 ty));
  [%expect {| universe 𝓤₀ : universe S 0 |}]
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
    m.ctx <- bind m.ctx (dn (Syntax.Named "x")) (Core.Universe Level.LZero);
    push m (GInfer (d (Surface.Var [ "x" ])));
    let tm, ty =
      match drive m with
      | PTermType (a, b) -> a, b
      | _ -> failwith "wrong shape"
    in
    Printf.printf
      "%s : %s"
      (Notation.pp_term (view_of_ctx m.ctx) tm)
      (Notation.pp_term (view_of_ctx m.ctx) (Evaluation.quote m.ctx.lvl ty)));
  [%expect {| x : universe 𝓤₀ |}]
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
    m.ctx <- bind m.ctx (dn (Syntax.Named "_")) (Core.Universe Level.LZero);
    push m (GInfer (d (Surface.Var [ "_" ])));
    let tm, ty =
      match drive m with
      | PTermType (a, b) -> a, b
      | _ -> failwith "wrong shape"
    in
    Printf.printf
      "%s : %s"
      (Notation.pp_term (view_of_ctx m.ctx) tm)
      (Notation.pp_term (view_of_ctx m.ctx) (Evaluation.quote m.ctx.lvl ty)));
  [%expect {| _ : universe 𝓤₀ |}]
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
       m.ctx <- bind m.ctx (dn Syntax.Anon) (Core.Universe Level.LZero);
       push m (GInfer (d (Surface.Var [ "_" ])));
       let _ = drive m in
       print_endline "UNEXPECTED: `_` resolved")
   with
   | Failure msg -> Printf.printf "rejected: %s" msg);
  [%expect {| rejected: Reporter.Message.NoVar_error |}]
;;

let%expect_test "infer Pi" =
  let p =
    d
      (Surface.Pi
         ( { name = dn (Named "x"); bound = d Surface.Universe; implicit = false }
         , d Surface.Universe ))
  in
  let tm, ty = infer_for_test p in
  Printf.printf
    "%s : %s"
    (Notation.pp_term Context_view.empty tm)
    (Notation.pp_term Context_view.empty (Evaluation.quote 0 ty));
  [%expect {| (x : universe 𝓤₀) -> universe 𝓤₀ : universe (S 0) ⊔ (S 0) |}]
;;

let%expect_test "check Lambda against Pi" =
  let p =
    d
      (Surface.Lambda
         { name = dn (Named "x"); bound = d (Surface.Var [ "x" ]); implicit = false })
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
    push m (GCheck (p, expected_ty));
    let tm =
      match drive m with
      | PTerm t -> t
      | _ -> failwith "wrong shape"
    in
    Printf.printf "%s" (Notation.pp_term (view_of_ctx m.ctx) tm));
  [%expect {| (fun x => x) |}]
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
    m.ctx <- bind m.ctx (dn (Syntax.Named "x")) (Core.Universe Level.LZero);
    let f_ty =
      Core.VPi
        ( { name = Named "a"; bound = Core.Universe Level.LZero; implicit = false }
        , fun _ -> Core.Universe Level.LZero )
    in
    m.ctx <- bind m.ctx (dn (Syntax.Named "f")) f_ty;
    push
      m
      (GInfer (d (Surface.App (false, d (Surface.Var [ "f" ]), d (Surface.Var [ "x" ])))));
    match drive m with
    | PTermType (tm, ty) ->
      Printf.printf
        "tm: %s\nty: %s"
        (Notation.pp_term (view_of_ctx m.ctx) tm)
        (Notation.pp_term (view_of_ctx m.ctx) (Evaluation.quote m.ctx.lvl ty))
    | _ -> failwith "wrong shape");
  [%expect
    {|
    tm: f x
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
    m.ctx <- bind m.ctx (dn (Syntax.Named "A")) (Core.Universe Level.LZero);
    m.ctx <- bind m.ctx (dn (Syntax.Named "x")) (Core.RigidLocal (0, Bwd.Emp));
    push m (GCheck (d (Surface.Goal (Some "here")), Core.RigidLocal (0, Bwd.Emp)));
    ignore (drive m);
    flush_goal_reports m;
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
    push m (GCheck (d (Surface.Goal None), Core.Universe Level.LZero));
    push m (GCheck (d (Surface.Goal None), Core.Universe Level.LZero));
    ignore (drive m);
    flush_goal_reports m;
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
    | Surface.Let { name; bindings; result_ty; body } ->
      GTopLet { loc; name; bindings; result_ty; body }
    | Surface.Data _ as d -> GTopData (loc, d)
    | Surface.Stack_def { name; params; signature; moves; clauses } ->
      GTopStackDef { loc; name; bindings = params; result_ty = signature; moves; clauses }
    | Surface.Elim_def { name; params; signature; opens; intros; target; clauses } ->
      GTopElimDef
        { loc
        ; name
        ; bindings = params
        ; result_ty = signature
        ; opens
        ; intros
        ; target
        ; clauses
        }
    | Surface.Axiom { name; bindings; result_ty } ->
      GTopAxiom { loc; name; bindings; result_ty }
    | Surface.Operator_decl _ ->
      Reporter.fatalf
        ~loc
        Elab_error
        "internal: Operator_decl reached elaboration (resolver should have consumed it)"
    | Surface.Record _ as r -> GTopRecord (loc, r)
  in
  push m g;
  ignore (drive m);
  flush_goal_reports ~def_name:(name_of_top top) m;
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
  let module_name = Syntax.Name.of_segments module_path in
  let file = Violet_surface.Op_resolver.resolve_module ~module_name file in
  Notation.run ~module_name
  @@ fun () ->
  Eio.traceln "checking [module] %s (%s)" module_name file.name;
  let kernel_module = Violet_kernel.Module.create () in
  Context.clear_level_vars ();
  let exports_set =
    let h = Hashtbl.create 16 in
    List.iter
      (fun (e : string Surface.spanned) -> Hashtbl.replace h e.value ())
      file.exports;
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
  let run_top (top : Surface.top Surface.spanned) =
    let loc = top.Surface.loc in
    try
      check_top ~module_name ~kernel_module ~goal_counter ~is_exported ~loc top.value
    with
    | Violet_kernel.Error.Kernel_error err ->
      Kernel_accept.report_rejection ~loc ~name:(name_of_top top.value) err
  in
  List.iter
    (fun (top : Surface.top Surface.spanned) ->
       Reporter.try_with
         ~fatal:(fun diag -> Reporter.emit_diagnostic diag)
         (fun () -> Reporter.merge_loc (Some top.Surface.loc) (fun () -> run_top top)))
    file.tops;
  let bound_names : (string, unit) Hashtbl.t = Hashtbl.create 16 in
  Yuujinchou.Trie.iter
    (fun path _ ->
       match Bwd.to_list path with
       | [] -> ()
       | seg :: _ -> Hashtbl.replace bound_names seg ())
    (Context.S.get_export ());
  let undefined =
    List.filter
      (fun (e : string Surface.spanned) -> not (Hashtbl.mem bound_names e.value))
      file.exports
  in
  List.iter
    (fun (e : string Surface.spanned) ->
       let name = e.Surface.value in
       let loc = e.Surface.loc in
       match Context.S.resolve [ name ] with
       | Some (ty, _) ->
         let cv = Violet_kernel.Context_view.make ~names:Bwd.Emp ~lvl:0 in
         let pp_ty = Notation.pp_term cv (Evaluation.quote 0 ty) in
         Observer.emit (Use { path = [ name ]; loc; def_loc = None; ty; pp_ty })
       | None -> ())
    file.exports;
  match undefined with
  | [] -> ()
  | names ->
    Reporter.fatalf
      Export_error
      "the following names are listed in \\export but never defined: %s"
      (String.concat ", " (List.map (fun (e : string Surface.spanned) -> e.value) names))
;;

let%expect_test "type-directed: bare zero against Nat resolves to Nat/zero" =
  let loc top = { Surface.loc = dloc; Surface.value = top } in
  let nat_data : Surface.top =
    Surface.Data
      { name = dn "Nat"
      ; params = []
      ; deps = []
      ; ind_ty = d Surface.Universe
      ; ctors =
          [ { name = dn (Named "zero")
            ; bound = d (Surface.Var [ "Nat" ])
            ; implicit = false
            }
          ; { name = dn (Named "suc")
            ; bound =
                d
                  (Surface.Pi
                     ( { name = dn Anon
                       ; bound = d (Surface.Var [ "Nat" ])
                       ; implicit = false
                       }
                     , d (Surface.Var [ "Nat" ]) ))
            ; implicit = false
            }
          ]
      }
  in
  let let_zero : Surface.top =
    Surface.Let
      { name = dn "x"
      ; bindings = []
      ; result_ty = d (Surface.Var [ "Nat" ])
      ; body = d (Surface.Var [ "zero" ])
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

let%expect_test
    "module: \\export of an inductive bundle: Nat, ctors, elim visible cross-module"
  =
  let loc top = { Surface.loc = dloc; Surface.value = top } in
  let nat_data : Surface.top =
    Surface.Data
      { name = dn "Nat"
      ; params = []
      ; deps = []
      ; ind_ty = d Surface.Universe
      ; ctors =
          [ { name = dn (Named "zero")
            ; bound = d (Surface.Var [ "Nat" ])
            ; implicit = false
            }
          ; { name = dn (Named "suc")
            ; bound =
                d
                  (Surface.Pi
                     ( { name = dn Anon
                       ; bound = d (Surface.Var [ "Nat" ])
                       ; implicit = false
                       }
                     , d (Surface.Var [ "Nat" ]) ))
            ; implicit = false
            }
          ]
      }
  in
  let mod_a : Surface.t =
    { name = "a.vt"; imports = []; exports = [ dn "Nat" ]; tops = [ loc nat_data ] }
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
               { name = dn "uses_bundle"
               ; bindings = []
               ; result_ty = d (Surface.Var [ "Nat" ])
               ; body = d (Surface.Var [ "Nat"; "zero" ])
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
  let loc top = { Surface.loc = dloc; Surface.value = top } in
  let nat_data : Surface.top =
    Surface.Data
      { name = dn "Nat"
      ; params = []
      ; deps = []
      ; ind_ty = d Surface.Universe
      ; ctors =
          [ { name = dn (Named "zero")
            ; bound = d (Surface.Var [ "Nat" ])
            ; implicit = false
            }
          ; { name = dn (Named "suc")
            ; bound =
                d
                  (Surface.Pi
                     ( { name = dn Anon
                       ; bound = d (Surface.Var [ "Nat" ])
                       ; implicit = false
                       }
                     , d (Surface.Var [ "Nat" ]) ))
            ; implicit = false
            }
          ]
      }
  in
  let point_record : Surface.top =
    Surface.Record
      { name = dn "Point"
      ; params = []
      ; ind_ty = d Surface.Universe
      ; fields =
          [ { name = dn (Named "x"); bound = d (Surface.Var [ "Nat" ]); implicit = false }
          ; { name = dn (Named "y"); bound = d (Surface.Var [ "Nat" ]); implicit = false }
          ]
      }
  in
  (* Module A: defines Nat + Point, exports only "Point" (which should cluster
     all five companions: Point, Point/mk, Point/x, Point/y, Point/elim). *)
  let mod_a : Surface.t =
    { name = "a.vt"
    ; imports = []
    ; exports = [ dn "Nat"; dn "Point" ]
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
               { name = dn "uses_proj"
               ; bindings = []
               ; result_ty =
                   d
                     (Surface.Pi
                        ( { name = dn Anon
                          ; bound = d (Surface.Var [ "Point" ])
                          ; implicit = false
                          }
                        , d (Surface.Var [ "Nat" ]) ))
               ; body = d (Surface.Var [ "Point/x" ])
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
  let dummy_loc = dloc in
  (* First declare Nat so fields can refer to it *)
  let nat_data : Surface.top =
    Surface.Data
      { name = dn "Nat"
      ; params = []
      ; deps = []
      ; ind_ty = d Surface.Universe
      ; ctors =
          [ { name = dn (Named "zero")
            ; bound = d (Surface.Var [ "Nat" ])
            ; implicit = false
            }
          ; { name = dn (Named "suc")
            ; bound =
                d
                  (Surface.Pi
                     ( { name = dn Anon
                       ; bound = d (Surface.Var [ "Nat" ])
                       ; implicit = false
                       }
                     , d (Surface.Var [ "Nat" ]) ))
            ; implicit = false
            }
          ]
      }
  in
  let point_record : Surface.top =
    Surface.Record
      { name = dn "Point"
      ; params = []
      ; ind_ty = d Surface.Universe
      ; fields =
          [ { name = dn (Named "x"); bound = d (Surface.Var [ "Nat" ]); implicit = false }
          ; { name = dn (Named "y"); bound = d (Surface.Var [ "Nat" ]); implicit = false }
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
    match Violet_kernel.Module.lookup kernel_module ("test/" ^ name) with
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
     Verifies that { fst => Nat/zero | snd => Nat/zero } : Pair Nat Nat
     elaborates to RecordIntro { name = "Pair"; fields = [("fst", ...); ("snd", ...)] }.
  *)
  let dummy_loc = dloc in
  let nat_data : Surface.top =
    Surface.Data
      { name = dn "Nat"
      ; params = []
      ; deps = []
      ; ind_ty = d Surface.Universe
      ; ctors =
          [ { name = dn (Named "zero")
            ; bound = d (Surface.Var [ "Nat" ])
            ; implicit = false
            }
          ; { name = dn (Named "suc")
            ; bound =
                d
                  (Surface.Pi
                     ( { name = dn Anon
                       ; bound = d (Surface.Var [ "Nat" ])
                       ; implicit = false
                       }
                     , d (Surface.Var [ "Nat" ]) ))
            ; implicit = false
            }
          ]
      }
  in
  let pair_record : Surface.top =
    Surface.Record
      { name = dn "Pair"
      ; params =
          [ { name = dn (Named "A"); bound = d Surface.Universe; implicit = false }
          ; { name = dn (Named "B"); bound = d Surface.Universe; implicit = false }
          ]
      ; ind_ty = d Surface.Universe
      ; fields =
          [ { name = dn (Named "fst"); bound = d (Surface.Var [ "A" ]); implicit = false }
          ; { name = dn (Named "snd"); bound = d (Surface.Var [ "B" ]); implicit = false }
          ]
      }
  in
  (* \let p : Pair Nat Nat => { fst => Nat/zero | snd => Nat/zero } *)
  let p_let : Surface.top =
    Surface.Let
      { name = dn "p"
      ; bindings = []
      ; result_ty =
          d
            (Surface.App
               ( false
               , d
                   (Surface.App
                      (false, d (Surface.Var [ "Pair" ]), d (Surface.Var [ "Nat" ])))
               , d (Surface.Var [ "Nat" ]) ))
      ; body =
          d
            (Surface.RecordLit
               [ dn "fst", d (Surface.Var [ "Nat"; "zero" ])
               ; dn "snd", d (Surface.Var [ "Nat"; "zero" ])
               ])
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
  (match Violet_kernel.Module.lookup kernel_module "test/p" with
   | Some (Violet_kernel.Module.Let { body; _ }) ->
     Printf.printf "body: %s\n" (Notation.pp_term Context_view.empty body)
   | _ -> Printf.printf "not found or wrong decl kind\n");
  [%expect {| body: Pair{ fst => Nat/zero | snd => Nat/zero } |}]
;;
