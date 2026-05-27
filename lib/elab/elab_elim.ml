(* Elimination elaboration: stack definitions, eliminator definitions,
   and inline elimination. *)

open Elab_common
module Syntax = Violet_kernel.Syntax
module Level = Violet_kernel.Level
module Pretty = Violet_kernel.Pretty
module Evaluation = Wiring.Eval
open Syntax
open Bwd
open Surface_utils

(* Substitute a list of (name, replacement) pairs into a Surface preterm.
   Only replaces Var [name] for single-segment paths; does not capture-avoid
   (record pattern binders are fresh relative to the body). *)
let rec subst_vars (env : (string * Surface.preterm) list) (t : Surface.preterm)
  : Surface.preterm
  =
  match t with
  | Surface.Var [ x ] ->
    (match List.assoc_opt x env with
     | Some replacement -> replacement
     | None -> t)
  | Surface.Var _ -> t
  | Surface.Located { loc; value } ->
    Surface.Located { loc; value = subst_vars env value }
  | Surface.App (impl, f, a) -> Surface.App (impl, subst_vars env f, subst_vars env a)
  | Surface.Lambda b ->
    let env' = List.filter (fun (x, _) -> Surface.Named x <> b.name) env in
    Surface.Lambda { b with bound = subst_vars env' b.bound }
  | Surface.TypedLambda (b, body) ->
    let env' = List.filter (fun (x, _) -> Surface.Named x <> b.name) env in
    Surface.TypedLambda ({ b with bound = subst_vars env b.bound }, subst_vars env' body)
  | Surface.Pi (b, cod) ->
    let env' = List.filter (fun (x, _) -> Surface.Named x <> b.name) env in
    Surface.Pi ({ b with bound = subst_vars env b.bound }, subst_vars env' cod)
  | Surface.Proj (e, f) -> Surface.Proj (subst_vars env e, f)
  | Surface.RecordLit entries ->
    Surface.RecordLit (List.map (fun (f, e) -> f, subst_vars env e) entries)
  | Surface.RecordUpdate (base, entries) ->
    Surface.RecordUpdate
      (subst_vars env base, List.map (fun (f, e) -> f, subst_vars env e) entries)
  | Surface.Max (a, b) -> Surface.Max (subst_vars env a, subst_vars env b)
  | Surface.Op_soup items ->
    Surface.Op_soup
      (List.map
         (function
           | Surface.SI_Atom e -> Surface.SI_Atom (subst_vars env e)
           | Surface.SI_Imp_arg e -> Surface.SI_Imp_arg (subst_vars env e)
           | other -> other)
         items)
  | Surface.Universe | Surface.Hole | Surface.Goal _ -> t
  | Surface.IdAbsurd _ -> t
  | Surface.Inline_elim _ -> t
;;

let rec walk_params
          ~(loc : Asai.Range.t)
          (ctx : local_ctx)
          (goal : Core.value)
          (bindings : Surface.pretype binder list)
  : local_ctx * Core.value
  =
  match bindings with
  | [] -> ctx, goal
  | b :: rest ->
    (match Evaluation.force_head goal with
     | Core.VPi ({ name = _; bound = a; implicit = _ }, k) ->
       let ctx' = bind ctx b.name a in
       let goal' = k (Core.RigidLocal (ctx.lvl, Bwd.Emp)) in
       walk_params ~loc ctx' goal' rest
     | other ->
       Reporter.fatalf
         ~loc
         Elab_error
         "stack-def: fewer Pi-layers than params, got `%s`"
         (Pretty.pp_term (view_of_ctx ctx) (Evaluation.quote ctx.lvl other)))
;;

(* `signature` and `n_params` are unchanged across recursion; they're used at
   the `<= split` site to reconstruct the result type as a Surface preterm
   (needed for the motive — a Hole there would over-capture and break
   pattern unification on constructor case args). *)
let rec walk_moves
          ~(loc : Asai.Range.t)
          (ctx : local_ctx)
          (goal : Core.value)
          (signature : Surface.pretype)
          (n_params : int)
          (moves : Surface.stack_move list)
          (clauses : Surface.clause list)
          (position : int)
  : Surface.preterm
  =
  let clause_loc (c : Surface.clause) = Option.value (loc_of c.body) ~default:loc in
  match moves with
  | [] ->
    (match clauses with
     | [ c ] -> c.body
     | cs ->
       Reporter.fatalf
         ~loc
         Elab_error
         "stack-def with no `<= split` requires exactly one clause, got %d"
         (List.length cs))
  | Surface.Intro :: rest ->
    (match Evaluation.force_head goal with
     | Core.VPi ({ name = _; bound = a; implicit = _ }, k) ->
       (* If this Intro is followed by Split, the clause pattern at this
          position is a constructor pattern (parsed as PVar/PCon) and the
          PVar's "name" is actually a constructor — don't use it as a
          binder name. *)
       let is_split_target =
         match rest with
         | Surface.Split :: _ -> true
         | _ -> false
       in
       let name =
         if is_split_target
         then Printf.sprintf "__x%d" position
         else pick_binder_name clauses position
       in
       let cod = k (Core.RigidLocal (ctx.lvl, Bwd.Emp)) in
       let ctx' = bind ctx (Syntax.Named name) a in
       let inner =
         walk_moves ~loc ctx' cod signature n_params rest clauses (position + 1)
       in
       Surface.Lambda { name = Syntax.Named name; bound = inner; implicit = false }
     | other ->
       Reporter.fatalf
         ~loc
         Elab_error
         "`<= intro` needs a function type, got `%s`"
         (Pretty.pp_term (view_of_ctx ctx) (Evaluation.quote ctx.lvl other)))
  | Surface.Split :: rest ->
    if rest <> []
    then
      Reporter.fatalf
        ~loc
        Elab_error
        "only one optional `<= split` is allowed, and it must come last";
    let target_name, target_ty =
      match ctx.names, ctx.types with
      | Bwd.Snoc (_, n), Bwd.Snoc (_, t) -> n, t
      | _ -> Reporter.fatalf ~loc Elab_error "`<= split` requires a preceding `<= intro`"
    in
    let pattern_position = position - 1 in
    (match Evaluation.force_head target_ty with
     | Core.VRecordType { name = r_name; fields; _ } ->
       if List.length clauses <> 1
       then
         Reporter.fatalf
           ~loc
           Elab_error
           "`<= split` on record `%s` expects exactly one clause, got %d"
           r_name
           (List.length clauses);
       let clause = List.hd clauses in
       let cloc = clause_loc clause in
       let entries =
         match List.nth_opt clause.patterns pattern_position with
         | Some (Surface.PRecord es) -> es
         | Some (Surface.PVar _) | Some (Surface.PImpVar _) | Some Surface.PWildcard ->
           Reporter.fatalf
             ~loc:cloc
             Elab_error
             "expected a record pattern `{ f = x, ... }` at split position for record \
              `%s`"
             r_name
         | Some (Surface.PCon _) ->
           Reporter.fatalf
             ~loc:cloc
             Elab_error
             "expected a record pattern `{ f = x, ... }` at split position for record \
              `%s`"
             r_name
         | None ->
           Reporter.fatalf
             ~loc:cloc
             Elab_error
             "clause `%s` has too few patterns"
             clause.head
       in
       let _ =
         List.fold_left
           (fun seen (fname, _) ->
              if List.mem fname seen
              then
                Reporter.fatalf
                  ~loc:cloc
                  Elab_error
                  "duplicate field `%s` in record pattern for `%s`"
                  fname
                  r_name
              else fname :: seen)
           []
           entries
       in
       let field_names =
         List.map
           (fun (b : Core.value_ty Syntax.binder) -> Syntax.Name.to_string b.name)
           fields
       in
       let entry_names = List.map fst entries in
       List.iter
         (fun fname ->
            if not (List.mem fname field_names)
            then
              Reporter.fatalf
                ~loc:cloc
                Elab_error
                "unknown field `%s` in record pattern for `%s`"
                fname
                r_name)
         entry_names;
       List.iter
         (fun fname ->
            if not (List.mem fname entry_names)
            then
              Reporter.fatalf
                ~loc:cloc
                Elab_error
                "missing field `%s` in record pattern for `%s`"
                fname
                r_name)
         field_names;
       (* Bind each field sub-pattern by substituting the projected value
          for the pattern variable in the clause body, in declaration order.
          Only PVar sub-patterns are supported. *)
       let subst_pairs =
         List.filter_map
           (fun fname ->
              let sub_pat = List.assoc fname entries in
              match sub_pat with
              | Surface.PVar v ->
                Some
                  ( v
                  , Surface.Proj (Surface.Var [ Syntax.Name.to_string target_name ], fname)
                  )
              | _ ->
                Reporter.fatalf
                  ~loc:cloc
                  Elab_error
                  "record pattern field `%s`: only simple variable sub-patterns are \
                   supported"
                  fname)
           field_names
       in
       subst_vars subst_pairs clause.body
     | Core.IndType (ind_head, _) ->
       let ctors =
         match Context.S.resolve [ ind_head ] with
         | Some (_, `Inductive info) -> Eliminator_synth.arities_of info
         | _ ->
           Reporter.fatalf ~loc Elab_error "`<= split`: `%s` is not an inductive" ind_head
       in
       (* A bare IDENT in a pattern position parses as PVar, but the user may
          have written the name of a nullary constructor. Normalize on-the-fly. *)
       let is_ctor name = List.exists (fun (n, _) -> String.equal n name) ctors in
       let normalize_pattern = function
         | Surface.PVar name when is_ctor name -> Surface.PCon (name, [])
         | p -> p
       in
       let seen = Hashtbl.create 4 in
       List.iter
         (fun (c : Surface.clause) ->
            let cloc = clause_loc c in
            match
              Option.map normalize_pattern (List.nth_opt c.patterns pattern_position)
            with
            | Some (Surface.PCon (cn, _)) ->
              if not (is_ctor cn)
              then
                Reporter.fatalf
                  ~loc:cloc
                  Elab_error
                  "`%s` is not a constructor of `%s`"
                  cn
                  ind_head;
              if Hashtbl.mem seen cn
              then
                Reporter.fatalf
                  ~loc:cloc
                  Elab_error
                  "constructor `%s` has more than one clause"
                  cn;
              Hashtbl.add seen cn ()
            | Some (Surface.PVar _) | Some (Surface.PImpVar _) | Some Surface.PWildcard ->
              Reporter.fatalf
                ~loc:cloc
                Elab_error
                "expected constructor pattern at split position, got variable"
            | Some (Surface.PRecord _) ->
              Reporter.fatalf
                ~loc:cloc
                Elab_error
                "expected constructor pattern at split position, got record pattern \
                 (target `%s` is an inductive, not a record)"
                ind_head
            | None ->
              Reporter.fatalf
                ~loc:cloc
                Elab_error
                "clause `%s` has too few patterns"
                c.head)
         clauses;
       let case_args : Surface.preterm list =
         List.map
           (fun (ctor_name, arity) ->
              let clause =
                match
                  List.find_opt
                    (fun (c : Surface.clause) ->
                       match
                         Option.map
                           normalize_pattern
                           (List.nth_opt c.patterns pattern_position)
                       with
                       | Some (Surface.PCon (cn, _)) -> String.equal cn ctor_name
                       | _ -> false)
                    clauses
                with
                | Some c -> c
                | None ->
                  Reporter.fatalf
                    ~loc
                    Elab_error
                    "`<= split` on `%s`: no clause for constructor `%s`"
                    ind_head
                    ctor_name
              in
              let cloc = clause_loc clause in
              let vs =
                match
                  Option.map
                    normalize_pattern
                    (List.nth_opt clause.patterns pattern_position)
                with
                | Some (Surface.PCon (_, vs)) -> vs
                | _ -> []
              in
              if List.length vs <> arity
              then
                Reporter.fatalf
                  ~loc:cloc
                  Elab_error
                  "constructor `%s` expects %d field-binders, got %d"
                  ctor_name
                  arity
                  (List.length vs);
              let v_names =
                List.map
                  (function
                    | Surface.PVar n -> n
                    | Surface.PImpVar n -> n
                    | Surface.PWildcard -> "_"
                    | Surface.PCon _ ->
                      Reporter.fatalf
                        ~loc:cloc
                        Elab_error
                        "`<= split`: deep constructor patterns not supported here"
                    | Surface.PRecord _ ->
                      Reporter.fatalf
                        ~loc:cloc
                        Elab_error
                        "`<= split`: record pattern not allowed inside a constructor")
                  vs
              in
              List.fold_right
                (fun v body ->
                   Surface.Lambda { name = Named v; bound = body; implicit = false })
                v_names
                clause.body)
           ctors
       in
       let motive_body =
         peel_pi_surface ~loc (pattern_position + 1 - n_params) signature
       in
       let motive : Surface.preterm =
         Surface.Lambda { name = target_name; bound = motive_body; implicit = false }
       in
       (* Extract the target's type as a Surface preterm so we can read off the
          data-type's params + deps to prepend to the eliminator's spine. The
          target's type is the domain of the (pattern_position - n_params)-th
          Pi-layer of `signature`. *)
       let target_type_surface : Surface.pretype =
         match List.nth_opt (pi_domain signature) (pattern_position - n_params) with
         | Some b -> b.bound
         | None ->
           Reporter.fatalf
             ~loc
             Elab_error
             "stack-def: cannot locate target type in signature"
       in
       let data_args : Surface.preterm list = Surface.applied_spine target_type_surface in
       List.fold_left
         (fun acc arg -> Surface.App (false, acc, arg))
         (Surface.Var [ ind_head; "elim" ])
         (data_args
          @ [ Surface.Var [ Syntax.Name.to_string target_name ]; motive ]
          @ case_args)
     | other ->
       Reporter.fatalf
         ~loc
         Elab_error
         "`<= split`: target type must be an inductive or record type, got `%s`"
         (Pretty.pp_term (view_of_ctx ctx) (Evaluation.quote ctx.lvl other)))
;;

(* --- Dispatch handlers --- *)

let handle_stack_def
      (m : machine)
      ~loc
      ~name
      ~name_loc
      ~bindings
      ~result_ty
      ~moves
      ~clauses
  =
  List.iter
    (fun (c : Surface.clause) ->
       List.iter
         (function
           | Surface.PImpVar n ->
             Reporter.fatalf
               ~loc
               Elab_error
               "`{%s}` patterns are only valid in `<= elim` definitions"
               n
           | _ -> ())
         c.patterns)
    clauses;
  let typ : Surface.pretype =
    List.fold_right
      (fun binding return_ty -> Surface.Pi (binding, return_ty))
      bindings
      result_ty
  in
  push
    m
    (KTopStackDef_HaveType
       { loc; name; name_loc; bindings; signature = result_ty; moves; clauses });
  push m (GInferType (loc, typ))
;;

let handle_stack_def_have_type
      (m : machine)
      ~loc
      ~name
      ~name_loc
      ~bindings
      ~signature
      ~moves
      ~clauses
  =
  match take_result m with
  | PType (typ_tm, _) ->
    let typ_val = Evaluation.eval m.ctx.env typ_tm in
    let ctx_inner, goal_inner = walk_params ~loc m.ctx typ_val bindings in
    let inner =
      walk_moves
        ~loc
        ctx_inner
        goal_inner
        signature
        (List.length bindings)
        moves
        clauses
        (List.length bindings)
    in
    let term : Surface.preterm =
      List.fold_right
        (fun (b : Surface.pretype binder) body ->
           Surface.Lambda { name = b.name; bound = body; implicit = b.implicit })
        bindings
        inner
    in
    push m (KTopLet_HaveBody { loc; name; name_loc; typ_tm; typ_val });
    push m (GCheck (loc, term, typ_val))
  | other ->
    Reporter.fatalf
      Elab_error
      "KTopStackDef_HaveType: bad result %s"
      ([%show: produced] other)
;;

let handle_elim_def
      (m : machine)
      ~loc
      ~name
      ~name_loc
      ~bindings
      ~result_ty
      ~opens
      ~intros
      ~target
      ~clauses
  =
  let typ : Surface.pretype =
    List.fold_right
      (fun binding return_ty -> Surface.Pi (binding, return_ty))
      bindings
      result_ty
  in
  push
    m
    (KTopElimDef_HaveType
       { loc
       ; name
       ; name_loc
       ; bindings
       ; signature = result_ty
       ; opens
       ; intros
       ; target
       ; clauses
       });
  push m (GInferType (loc, typ))
;;

let handle_elim_def_have_type
      (m : machine)
      ~loc
      ~name
      ~name_loc
      ~bindings
      ~signature
      ~opens
      ~intros
      ~target
      ~clauses
  =
  match take_result m with
  | PType (typ_tm, _) ->
    let typ_val = Evaluation.eval m.ctx.env typ_tm in
    let effective_intros =
      Inductive.compute_effective_intros ~loc ~bindings ~signature ~intros
    in
    let target_pos =
      let rec go i = function
        | [] ->
          Reporter.fatalf
            ~loc
            Elab_error
            "elim target `%s` not among effective intros"
            target
        | (x, _) :: _ when String.equal x target -> i
        | _ :: xs -> go (i + 1) xs
      in
      go 0 effective_intros
    in
    let target_type_value : Core.value =
      let rec peel v n lvl =
        if n = 0
        then (
          match Evaluation.force_head v with
          | Core.VPi ({ bound; _ }, _) -> bound
          | _ ->
            Reporter.fatalf
              ~loc
              Elab_error
              "elim: cannot extract target type — signature lacks target Pi-layer")
        else (
          match Evaluation.force_head v with
          | Core.VPi (_, k) -> peel (k (Core.rigid_local lvl)) (n - 1) (lvl + 1)
          | _ ->
            Reporter.fatalf
              ~loc
              Elab_error
              "elim: signature has fewer Pi-layers than required (need %d more)"
              n)
      in
      peel typ_val target_pos m.ctx.lvl
    in
    let elim_inner =
      Inductive.build_elim_body
        ~loc
        ~func_name:name
        ~params:bindings
        ~signature
        ~opens
        ~intros
        ~target
        ~clauses
        ~target_type_value
        ~start_lvl:m.ctx.lvl
    in
    let intros = effective_intros in
    let term : Surface.preterm =
      List.fold_right
        (fun (n, implicit) body ->
           Surface.Lambda { name = Named n; bound = body; implicit })
        intros
        elim_inner
    in
    push m (KTopLet_HaveBody { loc; name; name_loc; typ_tm; typ_val });
    push m (GCheck (loc, term, typ_val))
  | other ->
    Reporter.fatalf
      Elab_error
      "KTopElimDef_HaveType: bad result %s"
      ([%show: produced] other)
;;

let handle_check_inline_elim
      ~(infer_term :
         loc:Asai.Range.t -> local_ctx -> Surface.preterm -> Core.term * Core.value)
      (m : machine)
      loc
      (d : Surface.inline_elim_data)
      ty
  =
  match d.siblings with
  | [] ->
    emit_goal_report
      ~loc
      m
      ~name:(Printf.sprintf "<= \\elim %s (deferred)" d.target)
      ~target:ty;
    incr m.pending_goals;
    m.result <- Some (PTerm (Meta.fresh_goal m.ctx.lvl))
  | _ ->
    let raw_target_ty =
      match d.target_override with
      | Some override -> snd (infer_term ~loc m.ctx override)
      | None ->
        (match resolve_local m.ctx d.target with
         | Some ix -> local_type m.ctx ix
         | None ->
           Reporter.fatalf
             ~loc
             Elab_error
             "nested `<= \\elim %s`: target not in local scope"
             d.target)
    in
    let rec deep_resolve v =
      let v = Evaluation.force_head v in
      match v with
      | Core.RigidLocal (lvl, sp) ->
        let sp' = Bwd.map deep_resolve sp in
        (match List.assoc_opt lvl d.outer_subst with
         | Some bound -> deep_resolve (Evaluation.vapp_spine bound sp')
         | None -> Core.RigidLocal (lvl, sp'))
      | Core.Label (n, sp) -> Core.Label (n, Bwd.map deep_resolve sp)
      | Core.IndType (n, sp) -> Core.IndType (n, Bwd.map deep_resolve sp)
      | other -> other
    in
    let target_type_value = deep_resolve raw_target_ty in
    let resolved_ty = deep_resolve ty in
    let user_level_names =
      List.mapi (fun i n -> i, Syntax.Name.to_string n) (Bwd.to_list m.ctx.names)
    in
    let owner_map =
      match Evaluation.force_head target_type_value with
      | Core.IndType (ind_head, _) ->
        (match Context.S.resolve [ ind_head ] with
         | Some (_, `Inductive info) -> Readback.build_owner_map ~ind_head info
         | _ -> [])
      | _ -> []
    in
    let result_type_surface =
      Readback.readback_value_to_surface ~loc ~user_level_names ~owner_map resolved_ty
    in
    let expanded =
      Inductive.build_inline_elim_dispatch
        ~loc
        ~target_name:d.target
        ~target_type_raw:raw_target_ty
        ~target_type_value
        ~siblings:d.siblings
        ~result_type_surface
        ~start_lvl:m.ctx.lvl
        ~user_level_names
        ~outer_subst:d.outer_subst
        ~target_override:d.target_override
    in
    push m (GCheck (loc, expanded, ty))
;;
