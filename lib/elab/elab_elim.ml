(* Elimination elaboration: stack definitions, eliminator definitions,
   and inline elimination. *)

open Elab_common
open Violet_surface
open Violet_common
module Syntax = Violet_kernel.Syntax
module Pretty = Violet_kernel.Pretty
module Evaluation = Wiring.Eval
open Syntax
open Bwd
open Surface_utils

(* Synthesized Surface nodes inherit a location from the nearest source
   artifact (the clause body/head or the declaration's loc). *)
let at = Surface.Mk.at
let sn = Surface.Mk.sn

(* Substitute a list of (name, replacement) pairs into a Surface preterm.
   Only replaces Var [name] for single-segment paths; does not capture-avoid
   (record pattern binders are fresh relative to the body). *)
let rec subst_vars (env : (string * Surface.preterm) list) (t : Surface.preterm)
  : Surface.preterm
  =
  let keep node = { t with Surface.node } in
  match t.Surface.node with
  | Surface.Var [ x ] ->
    (match List.assoc_opt x env with
     | Some replacement -> replacement
     | None -> t)
  | Surface.Var _ -> t
  | Surface.App (impl, f, a) ->
    keep (Surface.App (impl, subst_vars env f, subst_vars env a))
  | Surface.Lambda b ->
    let env' = List.filter (fun (x, _) -> Surface.Named x <> b.name.Surface.value) env in
    keep (Surface.Lambda { b with bound = subst_vars env' b.bound })
  | Surface.TypedLambda (b, body) ->
    let env' = List.filter (fun (x, _) -> Surface.Named x <> b.name.Surface.value) env in
    keep
      (Surface.TypedLambda
         ({ b with bound = subst_vars env b.bound }, subst_vars env' body))
  | Surface.Pi (b, cod) ->
    let env' = List.filter (fun (x, _) -> Surface.Named x <> b.name.Surface.value) env in
    keep (Surface.Pi ({ b with bound = subst_vars env b.bound }, subst_vars env' cod))
  | Surface.Proj (e, f) -> keep (Surface.Proj (subst_vars env e, f))
  | Surface.RecordLit entries ->
    keep (Surface.RecordLit (List.map (fun (f, e) -> f, subst_vars env e) entries))
  | Surface.RecordUpdate (base, entries) ->
    keep
      (Surface.RecordUpdate
         (subst_vars env base, List.map (fun (f, e) -> f, subst_vars env e) entries))
  | Surface.Max (a, b) -> keep (Surface.Max (subst_vars env a, subst_vars env b))
  | Surface.Op_soup items ->
    keep
      (Surface.Op_soup
         (List.map
            (function
              | Surface.SI_Atom e -> Surface.SI_Atom (subst_vars env e)
              | Surface.SI_Imp_arg e -> Surface.SI_Imp_arg (subst_vars env e)
              | other -> other)
            items))
  | Surface.Hole | Surface.Goal _ -> t
  | Surface.IdAbsurd _ -> t
  | Surface.Absurd _ -> t
  | Surface.Inline_elim _ -> t
;;

let rec walk_params
          ~(loc : Asai.Range.t)
          (ctx : local_ctx)
          (goal : Core.value)
          (bindings : Surface.pretype Surface.sbinder list)
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
         (Notation.pp_term (view_of_ctx ctx) (Evaluation.quote ctx.lvl other)))
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
  let clause_loc (c : Surface.clause) = c.body.Surface.loc in
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
       let ctx' = bind ctx (sn loc (Syntax.Named name)) a in
       let inner =
         walk_moves ~loc ctx' cod signature n_params rest clauses (position + 1)
       in
       at
         inner.Surface.loc
         (Surface.Lambda
            { name = sn loc (Syntax.Named name); bound = inner; implicit = false })
     | other ->
       Reporter.fatalf
         ~loc
         Elab_error
         "`<= intro` needs a function type, got `%s`"
         (Notation.pp_term (view_of_ctx ctx) (Evaluation.quote ctx.lvl other)))
  | Surface.Split :: rest ->
    if rest <> []
    then
      Reporter.fatalf
        ~loc
        Elab_error
        "only one optional `<= split` is allowed, and it must come last";
    let target_name, target_ty =
      match ctx.names, ctx.types with
      | Bwd.Snoc (_, n), Bwd.Snoc (_, t) -> n.Surface.value, t
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
         match
           Option.map
             (fun (p : Surface.pattern) -> p.Surface.pnode)
             (List.nth_opt clause.patterns pattern_position)
         with
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
             clause.head.Surface.value
       in
       let _ =
         List.fold_left
           (fun seen ((fname, _) : string Surface.spanned * _) ->
              if List.mem fname.Surface.value seen
              then
                Reporter.fatalf
                  ~loc:cloc
                  Elab_error
                  "duplicate field `%s` in record pattern for `%s`"
                  fname.Surface.value
                  r_name
              else fname.Surface.value :: seen)
           []
           entries
       in
       let field_names =
         List.map
           (fun (b : Core.value_ty Syntax.binder) -> Syntax.Name.to_string b.name)
           fields
       in
       let entry_names =
         List.map (fun ((f, _) : string Surface.spanned * _) -> f.Surface.value) entries
       in
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
              let fspanned, sub_pat =
                List.find
                  (fun ((f, _) : string Surface.spanned * _) ->
                     String.equal f.Surface.value fname)
                  entries
              in
              match sub_pat.Surface.pnode with
              | Surface.PVar v ->
                Some
                  ( v
                  , at
                      cloc
                      (Surface.Proj
                         ( at cloc (Surface.Var [ Syntax.Name.to_string target_name ])
                         , fspanned )) )
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
       (* Normalize a bare-ident PVar that names a nullary constructor into a
          PCon; preserves the pattern's own location. *)
       let normalize_pattern (p : Surface.pattern) : Surface.pattern =
         match p.Surface.pnode with
         | Surface.PVar name when is_ctor name ->
           { p with
             Surface.pnode =
               Surface.PCon ({ Surface.loc = p.Surface.ploc; value = name }, [])
           }
         | _ -> p
       in
       let seen = Hashtbl.create 4 in
       List.iter
         (fun (c : Surface.clause) ->
            let cloc = clause_loc c in
            match
              Option.map normalize_pattern (List.nth_opt c.patterns pattern_position)
            with
            | Some { Surface.pnode = Surface.PCon (cn, _); ploc } ->
              if not (is_ctor cn.Surface.value)
              then
                Reporter.fatalf
                  ~loc:cn.Surface.loc
                  Elab_error
                  "`%s` is not a constructor of `%s`"
                  cn.Surface.value
                  ind_head;
              if Hashtbl.mem seen cn.Surface.value
              then
                Reporter.fatalf
                  ~loc:ploc
                  Elab_error
                  "constructor `%s` has more than one clause"
                  cn.Surface.value;
              Hashtbl.add seen cn.Surface.value ()
            | Some
                { Surface.pnode = Surface.PVar _ | Surface.PImpVar _ | Surface.PWildcard
                ; ploc
                } ->
              Reporter.fatalf
                ~loc:ploc
                Elab_error
                "expected constructor pattern at split position, got variable"
            | Some { Surface.pnode = Surface.PRecord _; ploc } ->
              Reporter.fatalf
                ~loc:ploc
                Elab_error
                "expected constructor pattern at split position, got record pattern \
                 (target `%s` is an inductive, not a record)"
                ind_head
            | None ->
              Reporter.fatalf
                ~loc:cloc
                Elab_error
                "clause `%s` has too few patterns"
                c.head.Surface.value)
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
                           (fun p -> (normalize_pattern p).Surface.pnode)
                           (List.nth_opt c.patterns pattern_position)
                       with
                       | Some (Surface.PCon (cn, _)) ->
                         String.equal cn.Surface.value ctor_name
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
              let pat = List.nth_opt clause.patterns pattern_position in
              let ploc =
                Option.fold
                  ~none:cloc
                  ~some:(fun (p : Surface.pattern) -> p.Surface.ploc)
                  pat
              in
              let vs =
                match Option.map (fun p -> (normalize_pattern p).Surface.pnode) pat with
                | Some (Surface.PCon (_, vs)) -> vs
                | _ -> []
              in
              if List.length vs <> arity
              then
                Reporter.fatalf
                  ~loc:ploc
                  Elab_error
                  "constructor `%s` expects %d field-binders, got %d"
                  ctor_name
                  arity
                  (List.length vs);
              let v_names =
                List.map
                  (fun (p : Surface.pattern) ->
                     match p.Surface.pnode with
                     | Surface.PVar n -> n
                     | Surface.PImpVar n -> n
                     | Surface.PWildcard -> "_"
                     | Surface.PCon _ ->
                       Reporter.fatalf
                         ~loc:p.Surface.ploc
                         Elab_error
                         "`<= split`: deep constructor patterns not supported here"
                     | Surface.PRecord _ ->
                       Reporter.fatalf
                         ~loc:p.Surface.ploc
                         Elab_error
                         "`<= split`: record pattern not allowed inside a constructor")
                  vs
              in
              List.fold_right
                (fun v body ->
                   at
                     cloc
                     (Surface.Lambda
                        { name = sn cloc (Named v); bound = body; implicit = false }))
                v_names
                clause.body)
           ctors
       in
       let motive_body = peel_pi_surface (pattern_position + 1 - n_params) signature in
       let motive : Surface.preterm =
         at
           motive_body.Surface.loc
           (Surface.Lambda
              { name = sn loc target_name; bound = motive_body; implicit = false })
       in
       (* Extract the target's type as a Surface preterm so we can read off the
          data-type's params + deps to prepend to the eliminator's spine. The
          target's type is the domain of the (pattern_position - n_params)-th
          Pi-layer of `signature`. *)
       let sig_index = pattern_position - n_params in
       if sig_index < 0
       then
         Reporter.fatalf
           ~loc
           Elab_error
           "`<= split` targets `%s : %s` which is a parameter; only arguments introduced \
            by `<= intro` after the parameters can be split on"
           (Syntax.Name.to_string target_name)
           (Notation.pp_term (view_of_ctx ctx) (Evaluation.quote ctx.lvl target_ty));
       let target_type_surface : Surface.pretype =
         match List.nth_opt (pi_domain signature) sig_index with
         | Some b -> b.bound
         | None ->
           Reporter.fatalf
             ~loc
             Elab_error
             "stack-def: cannot locate target type in signature"
       in
       let data_args : Surface.preterm list = Surface.applied_spine target_type_surface in
       Surface.apply
         (at loc (Surface.Var [ ind_head; "elim" ]))
         (data_args
          @ [ at loc (Surface.Var [ Syntax.Name.to_string target_name ]); motive ]
          @ case_args)
     | other ->
       Reporter.fatalf
         ~loc
         Elab_error
         "`<= split`: target type must be an inductive or record type, got `%s`"
         (Notation.pp_term (view_of_ctx ctx) (Evaluation.quote ctx.lvl other)))
;;

(* --- Dispatch handlers --- *)

let handle_stack_def (m : machine) ~loc ~name ~bindings ~result_ty ~moves ~clauses =
  List.iter
    (fun (c : Surface.clause) ->
       List.iter
         (fun (p : Surface.pattern) ->
            match p.Surface.pnode with
            | Surface.PImpVar n ->
              Reporter.fatalf
                ~loc:p.Surface.ploc
                Elab_error
                "`{%s}` patterns are only valid in `<= elim` definitions"
                n
            | _ -> ())
         c.patterns)
    clauses;
  let typ : Surface.pretype =
    List.fold_right
      (fun binding return_ty ->
         { Surface.loc = return_ty.Surface.loc; node = Surface.Pi (binding, return_ty) })
      bindings
      result_ty
  in
  push
    m
    (KTopStackDef_HaveType { loc; name; bindings; signature = result_ty; moves; clauses });
  push m (GInferType typ)
;;

let handle_stack_def_have_type
      (m : machine)
      ~loc
      ~name
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
        (fun (b : Surface.pretype Surface.sbinder) body ->
           at
             (Surface.join_loc b.name.Surface.loc body.Surface.loc)
             (Surface.Lambda { name = b.name; bound = body; implicit = b.implicit }))
        bindings
        inner
    in
    push m (KTopLet_HaveBody { loc; name; typ_tm; typ_val });
    push m (GCheck (term, typ_val))
  | other ->
    Reporter.fatalf Elab_error "KTopStackDef_HaveType: bad result %s" (produced_tag other)
;;

let handle_elim_def
      (m : machine)
      ~loc
      ~name
      ~bindings
      ~result_ty
      ~opens
      ~intros
      ~target
      ~clauses
  =
  let typ : Surface.pretype =
    List.fold_right
      (fun binding return_ty ->
         { Surface.loc = return_ty.Surface.loc; node = Surface.Pi (binding, return_ty) })
      bindings
      result_ty
  in
  push
    m
    (KTopElimDef_HaveType
       { loc; name; bindings; signature = result_ty; opens; intros; target; clauses });
  push m (GInferType typ)
;;

let handle_elim_def_have_type
      (m : machine)
      ~loc
      ~(name : string Surface.spanned)
      ~bindings
      ~signature
      ~opens
      ~intros
      ~target
      ~clauses
  =
  match take_result m with
  | PType (typ_tm, _) ->
    let name_loc = name.Surface.loc in
    let name = name.Surface.value in
    let typ_val = Evaluation.eval m.ctx.env typ_tm in
    (* The header carries spans on its intro names and elim target. The
       inductive synthesis machinery consumes bare strings, so strip spans
       at the boundary; the spans are reattached on the synthesized intro
       lambdas (below) and on the target Use event. *)
    let bare_intros = List.map (fun (s, b) -> s.Surface.value, b) intros in
    let target_str = target.Surface.value in
    (* name -> the source token's span, for intros the user wrote on the
       header line. Auto-filled params/implicits aren't in this map and fall
       back to the definition name's loc. *)
    let intro_span_of =
      let tbl = List.map (fun (s, _) -> s.Surface.value, s.Surface.loc) intros in
      fun n -> List.assoc_opt n tbl
    in
    let effective_intros =
      Inductive.compute_effective_intros ~loc ~bindings ~signature ~intros:bare_intros
    in
    let target_pos =
      let rec go i = function
        | [] ->
          Reporter.fatalf
            ~loc
            Elab_error
            "elim target `%s` not among effective intros"
            target_str
        | (x, _) :: _ when String.equal x target_str -> i
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
        ~intros:bare_intros
        ~target:target_str
        ~clauses
        ~target_type_value
        ~start_lvl:m.ctx.lvl
    in
    (* Emit a Use for the `\elim <target>` token: goto-def from it lands on
       the header intro that introduced the target. The target's type isn't
       trivially in hand here (it lives mid-Pi-tower); the intro Binder
       emitted by the lambda path below carries the type for hover, so this
       Use mainly provides goto-def back to the introducing token. We report
       the target's intro span as both loc (the elim token) and def_loc. *)
    (match intro_span_of target_str with
     | Some intro_loc ->
       let pp_ty =
         Notation.pp_term
           (view_of_ctx m.ctx)
           (Evaluation.quote m.ctx.lvl target_type_value)
       in
       Observer.emit
         (Use
            { path = [ target_str ]
            ; loc = target.Surface.loc
            ; def_loc = Some intro_loc
            ; ty = target_type_value
            ; pp_ty
            })
     | None -> ());
    (* Per-clause head Use: hovering a clause head shows the function's type;
       goto-def jumps to the `\let` name. Walked once here at the top level. *)
    let head_pp_ty =
      Notation.pp_term (view_of_ctx m.ctx) (Evaluation.quote m.ctx.lvl typ_val)
    in
    List.iter
      (fun (c : Surface.clause) ->
         Observer.emit
           (Use
              { path = [ c.head.Surface.value ]
              ; loc = c.head.Surface.loc
              ; def_loc = Some name_loc
              ; ty = typ_val
              ; pp_ty = head_pp_ty
              }))
      clauses;
    let intros = effective_intros in
    let term : Surface.preterm =
      List.fold_right
        (fun (n, implicit) body ->
           (* Each intro lambda binds at the header token the user wrote (so
              hover on `m`/`n` shows the right type); synthesized
              params/implicits with no source token fall back to the def
              name's loc. Using the def name's loc for every intro is what
              made hover on the def name wrongly show a binder. *)
           let bind_loc = Option.value (intro_span_of n) ~default:name_loc in
           at
             (Surface.join_loc bind_loc body.Surface.loc)
             (Surface.Lambda { name = sn bind_loc (Named n); bound = body; implicit }))
        intros
        elim_inner
    in
    publish_to_context ~exported:(m.is_exported name) [ name ] (typ_val, `Defn);
    push
      m
      (KTopElimDef_HaveBody
         { loc
         ; name = { Surface.loc = name_loc; value = name }
         ; typ_tm
         ; typ_val
         ; func_name = name
         ; target_pos
         });
    push m (GCheck (term, typ_val))
  | other ->
    Reporter.fatalf Elab_error "KTopElimDef_HaveType: bad result %s" (produced_tag other)
;;

(* Walks a Core.term and replaces applications of `Var func_name` where
   the argument at [target_pos] is `LocalVar k` with `LocalVar (k-1)`
   applied to the remaining arguments. Such an application is invoking
   the definition itself recursively, hence should be replaced by IH
   of eliminator.

   The IH is always at index field_index - 1 because the eliminator
   lambda-wrapping binds: λ field. λ ih. … *)
let rewrite_recursive_calls ~loc ~func_name ~target_pos term =
  let open Violet_kernel.Syntax.Core in
  let rec core_spine_of acc = function
    | App (f, a, impl) -> core_spine_of ((a, impl) :: acc) f
    | head -> head, acc
  in
  let rebuild_app head args =
    List.fold_left (fun f (a, impl) -> App (f, a, impl)) head args
  in
  let rec rw t =
    let rw_arg (a, impl) = rw a, impl in
    match t with
    | App _ ->
      let head, args = core_spine_of [] t in
      (match head with
       | Var n when String.equal n func_name ->
         if List.length args <= target_pos
         then
           Reporter.fatalf
             ~loc
             Elab_error
             "recursive call to `%s`: not enough arguments (need > %d, got %d)"
             func_name
             target_pos
             (List.length args);
         let target_arg, _ = List.nth args target_pos in
         (match target_arg with
          | LocalVar k ->
            let ih = LocalVar (k - 1) in
            let trailing = List.filteri (fun i _ -> i > target_pos) args in
            rebuild_app ih (List.map rw_arg trailing)
          | _ ->
            Reporter.fatalf
              ~loc
              Elab_error
              "non-structural recursive call to `%s` in clause body"
              func_name)
       | _ -> rebuild_app (rw head) (List.map rw_arg args))
    | Lambda b -> Lambda { b with bound = rw b.bound }
    | TypedLambda (b, body) -> TypedLambda ({ b with bound = rw b.bound }, rw body)
    | Pi (b, body) -> Pi ({ b with bound = rw b.bound }, rw body)
    | Lift r -> Lift { r with ty = rw r.ty }
    | LiftTerm r -> LiftTerm { r with ty = rw r.ty; tm = rw r.tm }
    | UnliftTerm r -> UnliftTerm { r with ty = rw r.ty; tm = rw r.tm }
    | RecordType r ->
      RecordType
        { r with
          params = List.map rw r.params
        ; fields =
            List.map
              (fun (b : typ Syntax.binder) -> { b with bound = rw b.bound })
              r.fields
        }
    | RecordIntro r ->
      RecordIntro { r with fields = List.map (fun (f, e) -> f, rw e) r.fields }
    | RecordProj r -> RecordProj { r with record = rw r.record }
    | IdAbsurd t -> IdAbsurd (rw t)
    | Empty -> Empty
    | Absurd t -> Absurd (rw t)
    | LocalVar _ | Var _ | Universe _ | Meta _ | InsertedMeta _ -> t
  in
  rw term
;;

let handle_elim_def_have_body
      (m : machine)
      ~loc
      ~(name : string Surface.spanned)
      ~typ_tm
      ~typ_val
      ~(func_name : string)
      ~(target_pos : int)
  =
  match take_result m with
  | PTerm term ->
    let name_loc = Some name.Surface.loc in
    let name = name.Surface.value in
    let term = rewrite_recursive_calls ~loc ~func_name ~target_pos term in
    let pp_ty =
      Notation.pp_term (view_of_ctx m.ctx) (Evaluation.quote m.ctx.lvl typ_val)
    in
    let refs = Axiom_deps.refs_in_term typ_tm @ Axiom_deps.refs_in_term term in
    Axiom_deps.register_def [ name ] ~refs;
    let axiom_deps = Axiom_deps.display_deps_of [ name ] in
    Observer.emit
      (Def
         { path = [ name ]
         ; module_path = Syntax.Name.to_segments m.module_name
         ; loc
         ; name_loc
         ; ty = typ_val
         ; pp_ty
         ; axiom_deps
         });
    let exported = m.is_exported name in
    let body_val = Evaluation.eval m.ctx.env term in
    publish_to_env ~exported [ name ] (body_val, `Defn);
    Env.register_definition name body_val;
    Notation.register_fold ~fn:name ~is_elim_head (Evaluation.quote 0 body_val);
    let qname = Syntax.Name.qualify m.module_name name in
    Kernel_accept.accept_let m.kernel_module ~loc ~name:qname ~ty:typ_tm ~body:term;
    m.result <- Some PUnit
  | other ->
    Reporter.fatalf Elab_error "KTopElimDef_HaveBody: bad result %s" (produced_tag other)
;;

let handle_check_inline_elim
      ~(infer_term : local_ctx -> Surface.preterm -> Core.term * Core.value)
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
      | Some override -> snd (infer_term m.ctx override)
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
      let resolve_arg (a : Core.arg) = { a with Core.tm = deep_resolve a.tm } in
      let v = Evaluation.force_head v in
      match v with
      | Core.RigidLocal (lvl, sp) ->
        let sp' = Bwd.map resolve_arg sp in
        (match List.assoc_opt lvl d.outer_subst with
         | Some bound -> deep_resolve (Evaluation.vapp_spine bound sp')
         | None -> Core.RigidLocal (lvl, sp'))
      | Core.Label (n, sp) -> Core.Label (n, Bwd.map resolve_arg sp)
      | Core.IndType (n, sp) -> Core.IndType (n, Bwd.map resolve_arg sp)
      | other -> other
    in
    let target_type_value = deep_resolve raw_target_ty in
    let resolved_ty = deep_resolve ty in
    let user_level_names =
      List.mapi
        (fun i n -> i, Syntax.Name.to_string n.Surface.value)
        (Bwd.to_list m.ctx.names)
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
    push m (GCheck (expanded, ty))
;;
