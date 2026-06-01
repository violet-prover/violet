(* Record elaboration: literal, update, projection, record type declarations. *)

open Elab_common
open Violet_surface
open Violet_common
module Syntax = Violet_kernel.Syntax
module Level = Violet_kernel.Level
module Pretty = Violet_kernel.Pretty
module Evaluation = Wiring.Eval
module Check = Wiring.Check
open Syntax
open Bwd

(* Check the field set of a record literal or update against the record's
   declared fields. Always rejects duplicates within [provided] and unknown
   names not in [expected_fields]; when [check_missing] is set, also rejects
   any expected field that isn't in [provided]. [ctx_label] is interpolated
   into error messages as "record <ctx_label>" (e.g. "literal", "update"). *)
let validate_record_fields
      ~(loc : Asai.Range.t)
      ~(ctx_label : string)
      ~(record_name : string)
      ~(expected_fields : string list)
      ~(provided : string list)
      ~(check_missing : bool)
  : unit
  =
  let _ : string list =
    List.fold_left
      (fun seen fname ->
         if List.mem fname seen
         then
           Reporter.fatalf
             ~loc
             Elab_error
             "duplicate field `%s` in record %s"
             fname
             ctx_label
         else fname :: seen)
      []
      provided
  in
  List.iter
    (fun fname ->
       if not (List.mem fname expected_fields)
       then
         Reporter.fatalf
           ~loc
           Elab_error
           "unknown field `%s` in record %s for `%s`"
           fname
           ctx_label
           record_name)
    provided;
  if check_missing
  then
    List.iter
      (fun fname ->
         if not (List.mem fname provided)
         then
           Reporter.fatalf
             ~loc
             Elab_error
             "missing field `%s` in record %s for `%s`"
             fname
             ctx_label
             record_name)
      expected_fields
;;

let walk_record_update_fields
      (m : machine)
      ~(loc : Asai.Range.t)
      ~(r_name : string)
      ~(overrides : (string * Surface.preterm) list)
      ~(base_core : Core.term)
      ~(done_rev : (string * Core.term) list)
      ~(fields : Core.typ Syntax.binder list)
      ~(eval_env : Core.value bwd)
  : unit
  =
  let rec go done_rev fields eval_env =
    match fields with
    | [] ->
      let result_fields = List.rev done_rev in
      m.result
      <- Some (PTerm (Core.RecordIntro { name = r_name; fields = result_fields }))
    | (b : Core.typ Syntax.binder) :: rest_fields ->
      let fname = Syntax.Name.to_string b.name in
      (match List.assoc_opt fname overrides with
       | Some expr ->
         let ty = Evaluation.eval eval_env b.Syntax.bound in
         push
           m
           (KRecordUpdate_Field
              (loc, r_name, base_core, overrides, done_rev, fname, rest_fields, eval_env));
         push m (GCheck (loc, expr, ty))
       | None ->
         let proj_core = Core.RecordProj { record = base_core; field = fname } in
         let proj_val = Evaluation.eval m.ctx.env proj_core in
         go ((fname, proj_core) :: done_rev) rest_fields (Bwd.Snoc (eval_env, proj_val)))
  in
  go done_rev fields eval_env
;;

(* --- Dispatch handlers --- *)

let handle_infer_record_lit (m : machine) (loc : Asai.Range.t) =
  ignore m;
  Reporter.fatalf
    ~loc
    Elab_error
    "cannot infer the type of a record literal; please annotate"
;;

let handle_check_record_lit
      (m : machine)
      (loc : Asai.Range.t)
      (entries : (string * Surface.preterm) list)
      (expected_ty : Core.value_ty)
  =
  match Evaluation.force_head expected_ty with
  | Core.VRecordType { name = r_name; fields = type_fields; field_env; field_terms; _ } ->
    let entry_names = List.map fst entries in
    let field_names =
      List.map
        (fun (b : Core.value_ty Syntax.binder) -> Syntax.Name.to_string b.name)
        type_fields
    in
    validate_record_fields
      ~loc
      ~ctx_label:"literal"
      ~record_name:r_name
      ~expected_fields:field_names
      ~provided:entry_names
      ~check_missing:true;
    (* Canonicalize entries to declaration order. `field_terms` is already
       in declaration order (eval.ml preserves order), parallel to `type_fields`. *)
    let canonical_entries =
      List.map (fun fname -> fname, List.assoc fname entries) field_names
    in
    (* The first field has no prior values to substitute, so
       `eval field_env t0.bound` reduces to the same value as
       `type_fields[0].bound`. *)
    (match canonical_entries, field_terms with
     | [], [] ->
       m.result <- Some (PTerm (Core.RecordIntro { name = r_name; fields = [] }))
     | (fname0, expr0) :: rest_entries, t0 :: rest_term_types ->
       let ty0 = Evaluation.eval field_env t0.Syntax.bound in
       push
         m
         (KRecordLit_Field
            (loc, r_name, [], fname0, rest_entries, rest_term_types, field_env));
       push m (GCheck (loc, expr0, ty0))
     | _ ->
       Reporter.fatalf ~loc Elab_error "internal: record literal field count mismatch")
  | Core.Flex _ ->
    Reporter.fatalf
      ~loc
      Elab_error
      "cannot infer record type for record literal; please annotate"
  | other ->
    Reporter.fatalf
      ~loc
      Elab_error
      "expected a record type for record literal, got %s"
      (Pretty.pp_term (view_of_ctx m.ctx) (Evaluation.quote m.ctx.lvl other))
;;

let handle_record_lit_field
      (m : machine)
      loc
      r_name
      done_rev
      current_fname
      remaining_entries
      remaining_term_binders
      eval_env
  =
  match take_result m with
  | PTerm field_tm ->
    let done_rev' = (current_fname, field_tm) :: done_rev in
    (* Evaluate the just-checked field term in the current local env to get
       its value, then extend `eval_env` with it so dependent types of later
       fields can substitute the actual value in place of the rigid-local
       placeholder VRecordType used at construction time. *)
    let field_val = Evaluation.eval m.ctx.env field_tm in
    let eval_env' = Bwd.Snoc (eval_env, field_val) in
    (match remaining_entries, remaining_term_binders with
     | [], [] ->
       let fields = List.rev done_rev' in
       m.result <- Some (PTerm (Core.RecordIntro { name = r_name; fields }))
     | (fname, expr) :: rest_entries, (t : Core.typ Syntax.binder) :: rest_term_types ->
       let ty = Evaluation.eval eval_env' t.Syntax.bound in
       push
         m
         (KRecordLit_Field
            (loc, r_name, done_rev', fname, rest_entries, rest_term_types, eval_env'));
       push m (GCheck (loc, expr, ty))
     | _ ->
       Reporter.fatalf
         Elab_error
         "internal: KRecordLit_Field: entry/type list length mismatch")
  | other ->
    Reporter.fatalf Elab_error "KRecordLit_Field: bad result %s" (produced_tag other)
;;

let handle_infer_record_update (m : machine) (loc : Asai.Range.t) =
  ignore m;
  Reporter.fatalf
    ~loc
    Elab_error
    "cannot infer the type of a record update; please annotate"
;;

let handle_check_record_update
      (m : machine)
      (loc : Asai.Range.t)
      (base : Surface.preterm)
      (overrides : (string * Surface.preterm) list)
      (expected_ty : Core.value_ty)
  =
  match Evaluation.force_head expected_ty with
  | Core.VRecordType { name = r_name; fields = type_fields; field_env; field_terms; _ } ->
    (match overrides with
     | [] ->
       Reporter.fatalf
         ~loc
         Elab_error
         "empty record update `{ _ | }`; use `p` directly instead"
     | _ -> ());
    let field_names =
      List.map
        (fun (b : Core.value_ty Syntax.binder) -> Syntax.Name.to_string b.name)
        type_fields
    in
    validate_record_fields
      ~loc
      ~ctx_label:"update"
      ~record_name:r_name
      ~expected_fields:field_names
      ~provided:(List.map fst overrides)
      ~check_missing:false;
    push m (KRecordUpdate_HaveBase (loc, r_name, overrides, field_terms, field_env));
    push m (GCheck (loc, base, expected_ty))
  | Core.Flex _ ->
    Reporter.fatalf
      ~loc
      Elab_error
      "cannot infer record type for record update; please annotate"
  | other ->
    Reporter.fatalf
      ~loc
      Elab_error
      "expected a record type for record update, got %s"
      (Pretty.pp_term (view_of_ctx m.ctx) (Evaluation.quote m.ctx.lvl other))
;;

let handle_record_update_have_base
      (m : machine)
      loc
      r_name
      overrides
      term_fields
      field_env
  =
  match take_result m with
  | PTerm base_core ->
    walk_record_update_fields
      m
      ~loc
      ~r_name
      ~overrides
      ~base_core
      ~done_rev:[]
      ~fields:term_fields
      ~eval_env:field_env
  | other ->
    Reporter.fatalf
      Elab_error
      "KRecordUpdate_HaveBase: bad result %s"
      (produced_tag other)
;;

let handle_record_update_field
      (m : machine)
      loc
      r_name
      base_core
      overrides
      done_rev
      current_fname
      remaining_term_fields
      eval_env
  =
  match take_result m with
  | PTerm field_tm ->
    let done_rev' = (current_fname, field_tm) :: done_rev in
    let field_val = Evaluation.eval m.ctx.env field_tm in
    let eval_env' = Bwd.Snoc (eval_env, field_val) in
    walk_record_update_fields
      m
      ~loc
      ~r_name
      ~overrides
      ~base_core
      ~done_rev:done_rev'
      ~fields:remaining_term_fields
      ~eval_env:eval_env'
  | other ->
    Reporter.fatalf Elab_error "KRecordUpdate_Field: bad result %s" (produced_tag other)
;;

let handle_infer_proj
      (m : machine)
      (loc : Asai.Range.t)
      (e : Surface.preterm)
      (f : string)
  =
  push m (KProj_HaveRec (loc, f));
  push m (GInfer (loc, e))
;;

let handle_proj_have_rec (m : machine) (loc : Asai.Range.t) (f : string) =
  match take_result m with
  | PTermType (e_core, v_ty) ->
    (match Evaluation.force_head v_ty with
     | Core.VRecordType { name = r_name; params = v_params; fields; _ } ->
       let field_names =
         List.map
           (fun (b : Core.value_ty Syntax.binder) -> Syntax.Name.to_string b.name)
           fields
       in
       if not (List.mem f field_names)
       then Reporter.fatalf ~loc Type_error "record `%s` has no field `%s`" r_name f;
       (* Look up the companion R/f to get its type, then apply it to params + record
          to recover the result type for this projection. *)
       let companion_name = r_name ^ "/" ^ f in
       let companion_ty = Context.lookup companion_name in
       let apply_vpi ty arg =
         match Evaluation.force_head ty with
         | Core.VPi (_, b) -> b arg
         | other ->
           Reporter.fatalf
             Elab_error
             "KProj_HaveRec: companion type is not a Pi when applying params, got %s"
             (Pretty.pp_term (view_of_ctx m.ctx) (Evaluation.quote m.ctx.lvl other))
       in
       let ty_after_params = List.fold_left apply_vpi companion_ty v_params in
       let v_record = Evaluation.eval m.ctx.env e_core in
       let result_ty = apply_vpi ty_after_params v_record in
       m.result
       <- Some (PTermType (Core.RecordProj { record = e_core; field = f }, result_ty))
     | Core.Flex _ ->
       Reporter.fatalf
         ~loc
         Elab_error
         "cannot infer record type for projection `.%s`; please annotate"
         f
     | other ->
       Reporter.fatalf
         ~loc
         Type_error
         "expected a record type for projection `.%s`, got %s"
         f
         (Pretty.pp_term (view_of_ctx m.ctx) (Evaluation.quote m.ctx.lvl other)))
  | other ->
    Reporter.fatalf Elab_error "KProj_HaveRec: bad result %s" (produced_tag other)
;;

let handle_top_record
      (m : machine)
      (loc : Asai.Range.t)
      (name : string)
      (params : Surface.pretype binder list)
      (ind_ty : Surface.pretype)
      (fields : Surface.pretype binder list)
  =
  (* Defensive check: implicit field binders are not supported.
     The parser does not emit them, but hand-constructed ASTs could. *)
  List.iter
    (fun (b : Surface.pretype binder) ->
       if b.implicit
       then
         Reporter.fatalf
           ~loc
           Elab_error
           "record `%s`: implicit field binders are not supported (`%s`)"
           name
           (Syntax.Name.to_string b.name))
    fields;
  let typ : Surface.pretype =
    List.fold_right
      (fun binding return_ty -> Surface.Pi (binding, return_ty))
      params
      ind_ty
  in
  push m (KTopRecord_HaveType (loc, name, params, ind_ty, fields));
  push m (GInferType (loc, typ))
;;

let handle_top_record_error (_m : machine) =
  Reporter.fatalf Elab_error "GTopRecord: payload is not Record"
;;

let handle_top_record_have_type
      ~(check_type : loc:Asai.Range.t -> local_ctx -> Surface.pretype -> Core.term)
      (m : machine)
      (loc : Asai.Range.t)
      (name : string)
      (params : Surface.pretype binder list)
      (ind_ty : Surface.pretype)
      (fields : Surface.pretype binder list)
  =
  match take_result m with
  | PType (typ_tm, _inferred_sort) ->
    let typ_val = Evaluation.eval m.ctx.env typ_tm in
    let ctx_with_params =
      (* Params extend ctx as rigid locals so field types can refer to them. *)
      let rec extend_params ctx = function
        | [] -> ctx
        | (b : Surface.pretype binder) :: rest ->
          let qty_tm = check_type ~loc ctx b.bound in
          let qty_val = Evaluation.eval ctx.env qty_tm in
          extend_params (bind ctx b.name qty_val) rest
      in
      extend_params m.ctx params
    in
    (* Check field types accumulating the local context.
       These Core terms have correct LocalVar indices: since m.ctx.lvl = 0 at
       top-level, params in ctx_with_params are at LocalVar (k-1-i), the same
       indices they will have under the k param-lambdas in head_body. *)
    let field_ty_terms, _ctx_after_fields =
      List.fold_left
        (fun (acc, ctx_acc) (b : Surface.pretype binder) ->
           let fty_tm = check_type ~loc ctx_acc b.bound in
           let fty_val = Evaluation.eval ctx_acc.env fty_tm in
           let ctx_acc' = bind ctx_acc b.name fty_val in
           acc @ [ b.name, fty_tm ], ctx_acc')
        ([], ctx_with_params)
        fields
    in
    let n_params = List.length params in
    let n_fields = List.length fields in
    let field_names = List.map (fun (b : Surface.pretype binder) -> b.name) fields in
    (* Field telescope built under k param-lambdas. The Core terms produced
       above were checked in ctx_with_params (depth k, m.ctx.lvl=0), so
       their LocalVar indices already match what RecordType needs under
       k param-lambdas; no re-check needed. *)
    let head_body : Core.term =
      (* Under k param-lambdas, param_i is at LocalVar (k-1-i) for i in [0,k-1]. *)
      let param_vars = List.init n_params (fun i -> Core.LocalVar (n_params - 1 - i)) in
      let core_fields =
        List.map
          (fun (fname, fty_tm) ->
             { Syntax.name = fname; bound = fty_tm; implicit = false })
          field_ty_terms
      in
      let record_ty_tm =
        Core.RecordType { name; params = param_vars; fields = core_fields }
      in
      List.fold_right
        (fun (b : Surface.pretype binder) body ->
           Core.Lambda { name = b.name; bound = body; implicit = b.implicit })
        params
        record_ty_tm
    in
    let exported = m.is_exported name in
    publish_to_context ~exported [ name ] (typ_val, `Defn);
    let head_body_val = Evaluation.eval m.ctx.env head_body in
    publish_to_env ~exported [ name ] (head_body_val, `Defn);
    Env.register_definition name head_body_val;
    let qname = m.module_name ^ "." ^ name in
    Kernel_accept.accept_let m.kernel_module ~loc ~name:qname ~ty:typ_tm ~body:head_body;
    let param_binder_core_terms =
      let _, terms =
        List.fold_left
          (fun (ctx_acc, acc) (b : Surface.pretype binder) ->
             let qty_tm = check_type ~loc ctx_acc b.bound in
             let qty_val = Evaluation.eval ctx_acc.env qty_tm in
             let ctx_acc' = bind ctx_acc b.name qty_val in
             ctx_acc', acc @ [ b.name, b.implicit, qty_tm ])
          (m.ctx, [])
          params
      in
      terms
    in
    let wrap_param_pis (inner : Core.term) : Core.term =
      List.fold_right
        (fun (n, impl, qty_tm) body ->
           Core.Pi ({ name = n; bound = qty_tm; implicit = impl }, body))
        param_binder_core_terms
        inner
    in
    (* Like wrap_param_pis but forces every param binder to be implicit.
       Field projectors can recover the params from the record argument's
       type, so users write `R/f r` rather than `R/f P₁…Pₖ r`. *)
    let wrap_param_pis_implicit (inner : Core.term) : Core.term =
      List.fold_right
        (fun (n, _impl, qty_tm) body ->
           Core.Pi ({ name = n; bound = qty_tm; implicit = true }, body))
        param_binder_core_terms
        inner
    in
    let wrap_param_lambdas (inner : Core.term) : Core.term =
      List.fold_right
        (fun (n, impl, _qty_tm) body ->
           Core.Lambda { name = n; bound = body; implicit = impl })
        param_binder_core_terms
        inner
    in
    let wrap_param_lambdas_implicit (inner : Core.term) : Core.term =
      List.fold_right
        (fun (n, _impl, _qty_tm) body ->
           Core.Lambda { name = n; bound = body; implicit = true })
        param_binder_core_terms
        inner
    in
    (* The application R P₁…Pₖ under (depth_extra) additional inner binders.
       Under the param Pi-tower (depth_extra more binders), the params are at:
       LocalVar(depth_extra + n_params - 1 - i) for param i in [0, k-1].
       Applied left-to-right: (((R P₁) P₂) ... Pₖ). *)
    let rec_applied_under (depth_extra : int) : Core.term =
      let base : Core.term = Core.Var name in
      let applied, _ =
        List.fold_left
          (fun (f, i) (_, impl, _qty_tm) ->
             Core.App (f, Core.LocalVar (depth_extra + n_params - 1 - i), impl), i + 1)
          (base, 0)
          param_binder_core_terms
      in
      applied
    in
    (* field_core_tys.(i) = Core.term for Tᵢ, valid under
       (params + f₁…fᵢ₋₁) binders *)
    let field_core_tys =
      let _, tys =
        List.fold_left
          (fun (ctx_acc, acc) (b : Surface.pretype binder) ->
             let fty_tm = check_type ~loc ctx_acc b.bound in
             let fty_val = Evaluation.eval ctx_acc.env fty_tm in
             let ctx_acc' = bind ctx_acc b.name fty_val in
             ctx_acc', acc @ [ fty_tm ])
          (ctx_with_params, [])
          fields
      in
      Array.of_list tys
    in
    (* R/mk: under k+n binders, fₙ=ix 0, ..., f₁=ix(n-1),
       Pₖ=ix n, ..., P₁=ix(k+n-1). *)
    let mk_name = name ^ "/mk" in
    let mk_ty : Core.term =
      (* Build the field Pi-tower inside the param Pi-tower.
         field_core_tys.(i) was checked in ctx of depth (k + i), so LocalVar indices
         in it are already correct for the Pi position at depth (k + i). *)
      let inner_result = rec_applied_under n_fields in
      let field_pi_tower =
        (* fold_right: process fields from last to first *)
        let n = n_fields in
        fst
        @@ List.fold_right
             (fun (b : Surface.pretype binder) (acc_body, i) ->
                (* i counts from 0 = last field; field index from start = n-1-i *)
                let field_idx = n - 1 - i in
                let fty = field_core_tys.(field_idx) in
                ( Core.Pi ({ name = b.name; bound = fty; implicit = false }, acc_body)
                , i + 1 ))
             fields
             (inner_result, 0)
      in
      wrap_param_pis field_pi_tower
    in
    let mk_body : Core.term =
      (* RecordIntro: field fᵢ (0-indexed) = LocalVar (n_fields - 1 - i) *)
      let intro_fields =
        List.mapi
          (fun i fname -> Syntax.Name.to_string fname, Core.LocalVar (n_fields - 1 - i))
          field_names
      in
      let intro = Core.RecordIntro { name; fields = intro_fields } in
      let with_field_lambdas =
        List.fold_right
          (fun (b : Surface.pretype binder) body ->
             Core.Lambda { name = b.name; bound = body; implicit = false })
          fields
          intro
      in
      wrap_param_lambdas with_field_lambdas
    in
    let mk_ty_val = Evaluation.eval m.ctx.env mk_ty in
    publish_to_context ~exported [ mk_name ] (mk_ty_val, `Defn);
    publish_to_context ~exported [ name; "mk" ] (mk_ty_val, `Defn);
    let mk_body_val = Evaluation.eval m.ctx.env mk_body in
    publish_to_env ~exported [ mk_name ] (mk_body_val, `Defn);
    Env.register_definition mk_name mk_body_val;
    let q_mk_name = m.module_name ^ "." ^ mk_name in
    Kernel_accept.accept_let m.kernel_module ~loc ~name:q_mk_name ~ty:mk_ty ~body:mk_body;
    let subst_proj_result_ty
          ~(n_before : int)
          ~(prev_field_names : string list)
          (tm : Core.term)
      : Core.term
      =
      let rec go extra_depth t =
        match t with
        | Core.LocalVar ix when ix < extra_depth -> t
        | Core.LocalVar ix ->
          let j = ix - extra_depth in
          if j < n_before
          then (
            (* field reference: replace with projection on r (at extra_depth below us) *)
            let field_idx = n_before - 1 - j in
            Core.RecordProj
              { record = Core.LocalVar extra_depth
              ; field =
                  (match List.nth_opt prev_field_names field_idx with
                   | Some v -> v
                   | None ->
                     Reporter.fatalf
                       ~loc
                       Elab_error
                       "record field projection: field index %d out of bounds (prev \
                        fields len=%d)"
                       field_idx
                       (List.length prev_field_names))
              })
          else
            (* deeper local from the outer context: shift down to account for the
               lost field binders, but add 1 for the new r binder *)
            Core.LocalVar (ix - n_before + 1)
        | Core.Universe _ -> t
        | Core.Var _ -> t
        | Core.App (a, b, implicit) ->
          Core.App (go extra_depth a, go extra_depth b, implicit)
        | Core.Lambda { name; bound; implicit } ->
          Core.Lambda { name; bound = go (extra_depth + 1) bound; implicit }
        | Core.TypedLambda ({ name; bound = dom; implicit }, body) ->
          Core.TypedLambda
            ({ name; bound = go extra_depth dom; implicit }, go (extra_depth + 1) body)
        | Core.Pi ({ name; bound = dom; implicit }, cod) ->
          Core.Pi
            ({ name; bound = go extra_depth dom; implicit }, go (extra_depth + 1) cod)
        | Core.Meta _ -> t
        | Core.InsertedMeta (mv, lvl) ->
          (* `InsertedMeta (m, lvl)` is sugar for `m` applied to the first `lvl`
             locals (levels 0..lvl-1).  Collapsing the prior-field binders into
             the single `r` changes those locals, so we cannot keep it opaque:
             expand the implicit spine into explicit applications and remap each
             argument through `go`.  At this node the term's local depth is
             `n_before + extra_depth`, so level L sits at index depth-1-L. *)
          let depth = n_before + extra_depth in
          let rec build acc lv =
            if lv >= lvl
            then acc
            else
              build
                (Core.App (acc, go extra_depth (Core.LocalVar (depth - 1 - lv)), false))
                (lv + 1)
          in
          build (Core.Meta mv) 0
        | Core.Lift { from_lvl; to_lvl; ty } ->
          Core.Lift { from_lvl; to_lvl; ty = go extra_depth ty }
        | Core.LiftTerm { from_lvl; to_lvl; ty; tm } ->
          Core.LiftTerm
            { from_lvl; to_lvl; ty = go extra_depth ty; tm = go extra_depth tm }
        | Core.UnliftTerm { from_lvl; to_lvl; ty; tm } ->
          Core.UnliftTerm
            { from_lvl; to_lvl; ty = go extra_depth ty; tm = go extra_depth tm }
        | Core.RecordType { name = rn; params = ps; fields = fs } ->
          let ps' = List.map (go extra_depth) ps in
          let fs', _ =
            List.fold_left
              (fun (acc, d) (b : Core.term Syntax.binder) ->
                 { b with bound = go d b.bound } :: acc, d + 1)
              ([], extra_depth)
              fs
          in
          Core.RecordType { name = rn; params = ps'; fields = List.rev fs' }
        | Core.RecordIntro { name = rn; fields = fs } ->
          Core.RecordIntro
            { name = rn; fields = List.map (fun (f, e) -> f, go extra_depth e) fs }
        | Core.RecordProj { record; field } ->
          Core.RecordProj { record = go extra_depth record; field }
        | Core.IdAbsurd t -> Core.IdAbsurd (go extra_depth t)
        | Core.Empty -> Core.Empty
        | Core.Absurd t -> Core.Absurd (go extra_depth t)
      in
      go 0 tm
    in
    List.iteri
      (fun i (b : Surface.pretype binder) ->
         let field_name = Syntax.Name.to_string b.name in
         let proj_name = name ^ "/" ^ field_name in
         (* prev_field_names: in context, last field bound = innermost.
            field_core_tys.(i) has LocalVar 0 = field_(i-1), ..., LocalVar (i-1) = field_0.
            So prev_field_names should map depth j -> field name at (i-1-j). *)
         let prev_field_names =
           Array.to_list (Array.sub (Array.of_list field_names) 0 i)
           |> List.map Syntax.Name.to_string
         in
         let proj_result_ty =
           subst_proj_result_ty ~n_before:i ~prev_field_names field_core_tys.(i)
         in
         (* ty = Pi({params...}, Pi(r:R_applied, proj_result_ty))
            Params are implicit on projectors: they are recovered from r's type. *)
         let proj_ty : Core.term =
           let r_pi =
             Core.Pi
               ( { name = Named "r"; bound = rec_applied_under 0; implicit = false }
               , proj_result_ty )
           in
           wrap_param_pis_implicit r_pi
         in
         let proj_body : Core.term =
           let proj_expr =
             Core.RecordProj { record = Core.LocalVar 0; field = field_name }
           in
           let with_r =
             Core.Lambda { name = Named "r"; bound = proj_expr; implicit = false }
           in
           wrap_param_lambdas_implicit with_r
         in
         let proj_ty_val = Evaluation.eval m.ctx.env proj_ty in
         publish_to_context ~exported [ proj_name ] (proj_ty_val, `Defn);
         (* Also register under the two-segment path [name; field_name] so that
            surface syntax `R/f` (parsed as Var [R; f]) can resolve the companion. *)
         publish_to_context ~exported [ name; field_name ] (proj_ty_val, `Defn);
         let proj_body_val = Evaluation.eval m.ctx.env proj_body in
         publish_to_env ~exported [ proj_name ] (proj_body_val, `Defn);
         Env.register_definition proj_name proj_body_val;
         let q_proj_name = m.module_name ^ "." ^ proj_name in
         Kernel_accept.accept_let
           m.kernel_module
           ~loc
           ~name:q_proj_name
           ~ty:proj_ty
           ~body:proj_body)
      fields;
    let ind_ty_tm = check_type ~loc m.ctx ind_ty in
    let elim_name = name ^ "/elim" in
    (* R/elim. M's type: R_applied → ind_ty, under k+1 binders (params+r).
       ind_ty_tm was checked in m.ctx (depth 0), so it has no local vars;
       under k+1 binders R_applied is at ix 0. *)
    let motive_ty_tm : Core.term =
      Core.Pi
        ( { name = Anon; bound = rec_applied_under 0; implicit = false }
        , shift_term 1 ind_ty_tm )
    in
    (* Build the case type: Pi(f₁:T₁, ..., Pi(fₙ:Tₙ', M (R/mk f₁...fₙ)))
       Under k+2 binders (params + r + M), then inside n more field binders.
       After all, we compute the case type.

       Let's number: under k+2+j binders when processing field j (0-indexed):
         fⱼ=ix 0, ..., f₁=ix(j-1), M=ix j, r=ix(j+1), Pₖ=ix(j+2),...

       Actually k+2 binders = P₁...Pₖ (k) + r (1) + M (1). Then inside field binders:
       Under all of them (k+2+n total):
         fₙ=ix 0, ..., f₁=ix(n-1), M=ix n, r=ix(n+1), Pₖ=ix(n+2),...,P₁=ix(k+n+1).

       R/mk has type Pi(params, Pi(fields, R params)).
       Applied to all params and fields under k+2+n binders:
         - Params: P₁=ix(k+n+1), P₂=ix(k+n), ..., Pₖ=ix(n+2). Left-to-right application.
         - Fields: f₁=ix(n-1), f₂=ix(n-2), ..., fₙ=ix 0. Left-to-right application.
       So R/mk applied = App(...App(App(Var mk_name, ix(k+n+1)), ix(k+n)),...ix(n+2), ix(n-1), ix(n-2),...ix 0).

       M applied to (R/mk applied) = App(LocalVar n, App(...R/mk applied...)).

       The case type inside n field binders:
         result = App(LocalVar n, R/mk_full_applied)
       field binder i (fold_right from last to first):
         T'ᵢ: field_core_tys.(i) in subst for case context.
         field_core_tys.(i) was checked in ctx of depth k+i (m.ctx + params + f₁...fᵢ₋₁).
         In case type context (depth k+2+i from outside = k+2 outer + i field binders):
           fᵢ₋₁=ix 0,...,f₁=ix(i-1),M=ix i,r=ix(i+1),Pₖ=ix(i+2),...,P₁=ix(i+k+1).
         field_core_tys.(i): LocalVar j for j in [0..i-1] = field, j in [i..i+k-1] = param.
         Shift by 2 (r and M added):
           LocalVar j -> LocalVar (j+2) for j >= 0.
         This is just shift_term 2.
    *)
    let case_ty_tm : Core.term =
      (* Build innermost: M(R/mk f₁...fₙ) under k+2+n binders.
         M = ix n, params P₁=ix(k+n+1)...Pₖ=ix(n+2), fields f₁=ix(n-1)...fₙ=ix 0. *)
      let mk_full_applied =
        let with_params =
          List.fold_left
            (fun f i ->
               (* Pᵢ (0-indexed from P₁) = ix(n_params+n_fields+1-i) under n_params+2+n_fields binders *)
               Core.App (f, Core.LocalVar (n_params + n_fields + 1 - i), true))
            (Core.Var mk_name)
            (List.init n_params (fun i -> i))
        in
        List.fold_left
          (fun f i ->
             (* fᵢ (0-indexed, f₁ first) = ix(n_fields-1-i) under k+2+n binders *)
             Core.App (f, Core.LocalVar (n_fields - 1 - i), false))
          with_params
          (List.init n_fields (fun i -> i))
      in
      let m_applied = Core.App (Core.LocalVar n_fields, mk_full_applied, false) in
      (* Wrap in field Pi-binders (fold_right: last field first) *)
      fst
      @@ List.fold_right
           (fun (b : Surface.pretype binder) (acc_body, i_rev) ->
              (* i_rev = 0 means last field, i = n_fields-1-i_rev *)
              let i = n_fields - 1 - i_rev in
              let fty = shift_term 2 field_core_tys.(i) in
              ( Core.Pi ({ name = b.name; bound = fty; implicit = false }, acc_body)
              , i_rev + 1 ))
           fields
           (m_applied, 0)
    in
    let elim_ty : Core.term =
      (* Under params + r + M + case binders: M=ix 1, r=ix 2. *)
      let m_r = Core.App (Core.LocalVar 1, Core.LocalVar 2, false) in
      let case_pi =
        Core.Pi ({ name = Named "case"; bound = case_ty_tm; implicit = false }, m_r)
      in
      let m_pi =
        Core.Pi ({ name = Named "M"; bound = motive_ty_tm; implicit = false }, case_pi)
      in
      let r_pi =
        Core.Pi ({ name = Named "r"; bound = rec_applied_under 0; implicit = false }, m_pi)
      in
      wrap_param_pis r_pi
    in
    (* Under k+3 binders: case=ix 0, M=ix 1, r=ix 2. *)
    let elim_body : Core.term =
      let r_var = Core.LocalVar 2 in
      let projections =
        List.map
          (fun fn -> Core.RecordProj { record = r_var; field = Syntax.Name.to_string fn })
          field_names
      in
      let inner =
        List.fold_left
          (fun f arg -> Core.App (f, arg, false))
          (Core.LocalVar 0)
          projections
      in
      let with_case =
        Core.Lambda { name = Named "case"; bound = inner; implicit = false }
      in
      let with_m =
        Core.Lambda { name = Named "M"; bound = with_case; implicit = false }
      in
      let with_r = Core.Lambda { name = Named "r"; bound = with_m; implicit = false } in
      wrap_param_lambdas with_r
    in
    let elim_ty_val = Evaluation.eval m.ctx.env elim_ty in
    publish_to_context ~exported [ elim_name ] (elim_ty_val, `Defn);
    (* Also register under two-segment path [name; "elim"] so that surface
       syntax `R/elim` (parsed as Var [R; "elim"]) can resolve the companion. *)
    publish_to_context ~exported [ name; "elim" ] (elim_ty_val, `Defn);
    let elim_body_val = Evaluation.eval m.ctx.env elim_body in
    publish_to_env ~exported [ elim_name ] (elim_body_val, `Defn);
    Env.register_definition elim_name elim_body_val;
    let q_elim_name = m.module_name ^ "." ^ elim_name in
    Kernel_accept.accept_let
      m.kernel_module
      ~loc
      ~name:q_elim_name
      ~ty:elim_ty
      ~body:elim_body;
    m.result <- Some PUnit
  | other ->
    Reporter.fatalf Elab_error "KTopRecord_HaveType: bad result %s" (produced_tag other)
;;
