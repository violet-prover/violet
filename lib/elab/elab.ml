module Syntax = Violet_kernel.Syntax
module Level = Violet_kernel.Level
module Context_view = Violet_kernel.Context_view
module Pretty = Violet_kernel.Pretty
module Evaluation = Wiring.Eval
module Check = Wiring.Check
module Unification = Unify
open Syntax
open Asai.Range
open Bwd
open Surface_utils

(* local_ctx tracks:
   - env:   values for de Bruijn indexing during eval
   - types: types of the same locals, for type-checking lookup
   - names: surface names of the same locals, for surface→core resolution
   - lvl:   current de Bruijn level (= Bwd.length env), threaded for fresh metas
   All four grow together — `extend` keeps them in sync. *)
type local_ctx =
  { env : Core.value bwd
  ; types : Core.value bwd
  ; names : Syntax.binder_name bwd
  ; lvl : int
  }

let empty_ctx : local_ctx = { env = Emp; types = Emp; names = Emp; lvl = 0 }

let extend
      (ctx : local_ctx)
      (name : Syntax.binder_name)
      (ty : Core.value)
      (value : Core.value)
  : local_ctx
  =
  { env = Bwd.Snoc (ctx.env, value)
  ; types = Bwd.Snoc (ctx.types, ty)
  ; names = Bwd.Snoc (ctx.names, name)
  ; lvl = ctx.lvl + 1
  }
;;

let view_of_ctx (ctx : local_ctx) : Context_view.t =
  Context_view.make ~names:(Bwd.map Syntax.Name.to_string ctx.names) ~lvl:ctx.lvl
;;

let bind (ctx : local_ctx) (name : Syntax.binder_name) (ty : Core.value) : local_ctx =
  extend ctx name ty (Core.RigidLocal (ctx.lvl, Emp))
;;

(* Look up a surface name in the local context.  Returns the de Bruijn INDEX
   (innermost = 0) if found, or None if it's a global. `Anon` binders carry
   no string name, so they never match. *)
let resolve_local (ctx : local_ctx) (x : string) : int option =
  let rec go i = function
    | Emp -> None
    | Snoc (_, Syntax.Named n) when String.equal n x -> Some i
    | Snoc (rest, _) -> go (i + 1) rest
  in
  go 0 ctx.names
;;

let resolve_universe_var (x : string) : Level.level option =
  if Context.is_level_var x then Some (Level.LVar x) else None
;;

let local_type (ctx : local_ctx) (ix : int) : Core.value =
  let rec nth env i =
    match env, i with
    | Snoc (_, v), 0 -> v
    | Snoc (rest, _), k -> nth rest (k - 1)
    | Emp, _ -> Reporter.fatalf Elab_error "local index %d out of range in types" ix
  in
  nth ctx.types ix
;;

(* If the first clause has a PVar at that position, reuse it; otherwise
   (e.g. PCon at a split site) synthesize a fresh name. *)
let pick_binder_name (clauses : Surface.clause list) (position : int) : string =
  match clauses with
  | [] -> Printf.sprintf "__x%d" position
  | { patterns; _ } :: _ ->
    (match List.nth_opt patterns position with
     | Some (Surface.PVar v) -> v
     | _ -> Printf.sprintf "__x%d" position)
;;

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
         (Pretty.pp_value (view_of_ctx ctx) other))
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
         (Pretty.pp_value (view_of_ctx ctx) other))
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
       let normalize = function
         | Surface.PVar name when is_ctor name -> Surface.PCon (name, [])
         | p -> p
       in
       let seen = Hashtbl.create 4 in
       List.iter
         (fun (c : Surface.clause) ->
            let cloc = clause_loc c in
            match Option.map normalize (List.nth_opt c.patterns pattern_position) with
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
                         Option.map normalize (List.nth_opt c.patterns pattern_position)
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
                  Option.map normalize (List.nth_opt clause.patterns pattern_position)
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
         (Pretty.pp_value (view_of_ctx ctx) other))
;;

type produced =
  | PTerm of Core.term
  | PTermType of Core.term * Core.value_ty
  | PType of Core.term * Level.level
  | PUnit
[@@deriving show]

type goal =
  | GCheck of t * Surface.preterm * Core.value_ty
  | GInfer of t * Surface.preterm
  | GInferType of t * Surface.pretype
  | KCheckBy_Infer of t * Core.value_ty
  | KApp_HaveFn of t * bool * Surface.preterm
  | KApp_HaveArg of t * Core.term * (Core.value -> Core.value)
  | KPi_HaveDom of t * Syntax.binder_name * bool * Surface.pretype
  | KPi_HaveCod of t * Syntax.binder_name * bool * Core.term * Level.level
  | KLam_Body of t * Syntax.binder_name * bool
  | KTypedLam_HaveDom of t * Syntax.binder_name * bool * Surface.preterm
  | KTypedLam_HaveBody of t * Syntax.binder_name * bool * Core.term * Core.value_ty
  | KMax_HaveLeft of t * Surface.preterm
  | KMax_HaveRight of t * Level.level
  | KEnsureUniverse of t
  | KIdAbsurd_HaveArg of t
  | GTopLet of
      t * string * Surface.pretype binder list * Surface.pretype * Surface.preterm
  | GTopData of t * Surface.top
  | GTopUniverseDecl of string list
  | GTopStackDef of
      t
      * string
      * Surface.pretype binder list
      * Surface.pretype
      * Surface.stack_move list
      * Surface.clause list
  | KTopLet_HaveType of t * string * Surface.preterm * Surface.pretype binder list
  | KTopLet_HaveBody of t * string * Core.term * Core.value_ty
  | KTopData_HaveType of
      t
      * string
      * Surface.pretype binder list
      * Surface.pretype binder list
      * Surface.pretype
      * Surface.pretype binder list
  | KTopStackDef_HaveType of
      t
      * string
      * Surface.pretype binder list
      * Surface.pretype
      * Surface.stack_move list
      * Surface.clause list
  | GTopElimDef of
      t
      * string
      * Surface.pretype binder list
      * Surface.pretype
      * string list
      * (string * bool) list
      * string
      * Surface.clause list
  | KTopElimDef_HaveType of
      t
      * string
      * Surface.pretype binder list
      * Surface.pretype
      * string list
      * (string * bool) list
      * string
      * Surface.clause list
  | GTopRecord of t * Surface.top
  | KTopRecord_HaveType of
      t
      * string
      * Surface.pretype binder list
      * Surface.pretype
      * Surface.pretype binder list
  (* Continuation frame for check-mode record literal elaboration.
     Fired after each field's GCheck completes.
     - r_name:            bare record name (for RecordIntro)
     - done_rev:          (field_name, core_term) pairs checked so far, in reverse
     - current_fname:     name of the field just checked (the GCheck we just returned from)
     - remaining_entries: (name, surface_expr) pairs in declaration order, still to check
     - remaining_term_binders: term-form field binders for remaining fields, used to
                          re-evaluate dependent field types with actual prior values.
     - eval_env:          VRecordType.field_env extended with the VALUES of every field
                          checked so far. Evaluating the next remaining term binder's
                          bound term in this env substitutes prior field values into the
                          dependent type. *)
  | KRecordLit_Field of
      t
      * string
      * (string * Core.term) list
      * string
      * (string * Surface.preterm) list
      * Core.typ Syntax.binder list
      * Core.value bwd
  (* Continuation for GInfer (Proj (e, f)): holds (loc, field_name) after e is inferred. *)
  | KProj_HaveRec of t * string
  (* Continuation for GCheck (RecordUpdate …, expected_ty): fired after base is checked.
     - loc:               source location (for nested GChecks)
     - r_name:            record name (for RecordIntro)
     - overrides:         (field_name, surface_expr) map of the user-supplied overrides
     - term_fields:       full term-form field binders, declaration order
     - eval_env:          field_env from VRecordType — extended with each chosen field
                          value as the walk progresses, so dependent field types can be
                          instantiated on the fly. *)
  | KRecordUpdate_HaveBase of
      t
      * string
      * (string * Surface.preterm) list
      * Core.typ Syntax.binder list
      * Core.value bwd
  (* Continuation for each override field inside RecordUpdate.
     Fired after each GCheck for an override field completes.
     - loc:               source location
     - r_name:            record name
     - base_core:         elaborated base term (for projections of non-overridden fields)
     - overrides:         the full overrides map
     - done_rev:          (field_name, core_term) pairs checked so far, in reverse order
     - current_fname:     name of the field whose GCheck just completed
     - remaining_term_fields: remaining term-form binders still to process
     - eval_env:          extended with the values of every field chosen so far
                          (overrides as well as projections from base). *)
  | KRecordUpdate_Field of
      t
      * string
      * Core.term
      * (string * Surface.preterm) list
      * (string * Core.term) list
      * string
      * Core.typ Syntax.binder list
      * Core.value bwd

type machine =
  { mutable goals : goal list
  ; mutable result : produced option
  ; mutable ctx : local_ctx
  ; mutable saved_ctx : local_ctx list
  ; module_name : string
  ; kernel_module : Violet_kernel.Module.t
  ; goal_counter : int ref
  ; pending_goals : int ref
  ; is_exported : string -> bool
  }

let make_machine
      ~(module_name : string)
      ~(kernel_module : Violet_kernel.Module.t)
      ~(goal_counter : int ref)
      ?(is_exported = fun _ -> false)
      ()
  : machine
  =
  { goals = []
  ; result = None
  ; ctx = empty_ctx
  ; saved_ctx = []
  ; module_name
  ; kernel_module
  ; goal_counter
  ; pending_goals = ref 0
  ; is_exported
  }
;;

let save_ctx (m : machine) : unit = m.saved_ctx <- m.ctx :: m.saved_ctx

let restore_ctx (m : machine) : unit =
  match m.saved_ctx with
  | c :: rest ->
    m.ctx <- c;
    m.saved_ctx <- rest
  | [] -> Reporter.fatalf Elab_error "Elab: restore_ctx on empty saved_ctx"
;;

let push (m : machine) (g : goal) : unit = m.goals <- g :: m.goals

let take_result (m : machine) : produced =
  match m.result with
  | Some p ->
    m.result <- None;
    p
  | None -> Reporter.fatalf Elab_error "Elab: take_result on empty result"
;;

let resolve_goal_name (m : machine) (n : string option) : string =
  match n with
  | Some s -> s
  | None ->
    let i = !(m.goal_counter) in
    m.goal_counter := i + 1;
    string_of_int i
;;

let emit_goal_report
      ~(loc : Asai.Range.t)
      (m : machine)
      ~(name : string)
      ~(target : Core.value)
  : unit
  =
  let buf = Buffer.create 128 in
  Buffer.add_string buf (Printf.sprintf "%s/?%s\n" m.module_name name);
  Buffer.add_string buf "  --- context ---\n";
  (* Bwd.to_list returns outermost-first. *)
  let names = List.map Syntax.Name.to_string (Bwd.to_list m.ctx.names) in
  let types = Bwd.to_list m.ctx.types in
  List.iter2
    (fun n ty ->
       Buffer.add_string
         buf
         (Printf.sprintf "  %s : %s\n" n (Pretty.pp_value (view_of_ctx m.ctx) ty)))
    names
    types;
  Buffer.add_string buf "  --- target ---\n";
  Buffer.add_string
    buf
    (Printf.sprintf "  %s" (Pretty.pp_value (view_of_ctx m.ctx) target));
  Reporter.emitf ~loc Goal_report "%s" (Buffer.contents buf)
;;

let name_of_top : Surface.top -> string = function
  | Surface.Let (n, _, _, _) -> n
  | Surface.Data { name; _ } -> name
  | Surface.Stack_def { name; _ } -> name
  | Surface.Elim_def { name; _ } -> name
  | Surface.Universe_decl _ -> "<universe_decl>"
  | Surface.Operator_decl _ -> "<operator_decl>"
  | Surface.Record { name; _ } -> name
;;

let publish_to_context ~exported path datum =
  if exported
  then
    Context.S.include_singleton
      ~context_visible:`Visible
      ~context_export:`Export
      (path, datum)
  else Context.S.import_singleton ~context_visible:`Visible (path, datum)
;;

let publish_to_env ~exported path datum =
  if exported
  then
    Env.S.include_singleton ~context_visible:`Visible ~context_export:`Export (path, datum)
  else Env.S.import_singleton ~context_visible:`Visible (path, datum)
;;

(* Shift all free LocalVar indices in a Core.term by `n`.
   Variables with index < cutoff (bound by binders we're inside) are left alone.
   This is the standard weakening operation for de Bruijn terms. *)
let rec shift_term ?(cutoff = 0) (n : int) (t : Core.term) : Core.term =
  match t with
  | Core.LocalVar ix -> if ix >= cutoff then Core.LocalVar (ix + n) else t
  | Core.Universe _ | Core.Var _ | Core.Meta _ | Core.InsertedMeta _ -> t
  | Core.App (a, b) -> Core.App (shift_term ~cutoff n a, shift_term ~cutoff n b)
  | Core.Lambda { name; bound; implicit } ->
    Core.Lambda { name; bound = shift_term ~cutoff:(cutoff + 1) n bound; implicit }
  | Core.TypedLambda ({ name; bound = dom; implicit }, body) ->
    Core.TypedLambda
      ( { name; bound = shift_term ~cutoff n dom; implicit }
      , shift_term ~cutoff:(cutoff + 1) n body )
  | Core.Pi ({ name; bound = dom; implicit }, cod) ->
    Core.Pi
      ( { name; bound = shift_term ~cutoff n dom; implicit }
      , shift_term ~cutoff:(cutoff + 1) n cod )
  | Core.Lift { from_lvl; to_lvl; ty } ->
    Core.Lift { from_lvl; to_lvl; ty = shift_term ~cutoff n ty }
  | Core.LiftTerm { from_lvl; to_lvl; ty; tm } ->
    Core.LiftTerm
      { from_lvl; to_lvl; ty = shift_term ~cutoff n ty; tm = shift_term ~cutoff n tm }
  | Core.UnliftTerm { from_lvl; to_lvl; ty; tm } ->
    Core.UnliftTerm
      { from_lvl; to_lvl; ty = shift_term ~cutoff n ty; tm = shift_term ~cutoff n tm }
  | Core.RecordType { name = rn; params; fields } ->
    let params' = List.map (shift_term ~cutoff n) params in
    let fields', _ =
      List.fold_left
        (fun (acc, c) (b : Core.term Syntax.binder) ->
           { b with bound = shift_term ~cutoff:c n b.bound } :: acc, c + 1)
        ([], cutoff)
        fields
    in
    Core.RecordType { name = rn; params = params'; fields = List.rev fields' }
  | Core.RecordIntro { name = rn; fields } ->
    Core.RecordIntro
      { name = rn; fields = List.map (fun (f, e) -> f, shift_term ~cutoff n e) fields }
  | Core.RecordProj { record; field } ->
    Core.RecordProj { record = shift_term ~cutoff n record; field }
  | Core.IdAbsurd t -> Core.IdAbsurd (shift_term ~cutoff n t)
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

let rec dispatch (m : machine) (g : goal) : unit =
  match g with
  | GInfer (loc, Located { loc = loc'; value }) ->
    push m (GInfer (Option.get loc', value));
    ignore loc
  | GCheck (loc, Located { loc = loc'; value }, ty) ->
    push m (GCheck (Option.get loc', value, ty));
    ignore loc
  | GInferType (loc, Located { loc = loc'; value }) ->
    push m (GInferType (Option.get loc', value));
    ignore loc
  | GInfer (_, Universe) ->
    m.result
    <- Some
         (PTermType (Core.Universe Level.LZero, Core.Universe (Level.LSuc Level.LZero)))
  | GInfer (_, Var [ x ]) ->
    (match resolve_local m.ctx x with
     | Some i -> m.result <- Some (PTermType (Core.LocalVar i, local_type m.ctx i))
     | None ->
       (match resolve_universe_var x with
        | Some l ->
          m.result <- Some (PTermType (Core.Universe l, Core.Universe (Level.lsuc l)))
        | None -> m.result <- Some (PTermType (Core.Var x, Context.lookup x))))
  | GInfer (loc, Var path) ->
    let _ = loc in
    let ty = Context.lookup_path path in
    let joined = String.concat "/" path in
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
            (Pretty.pp_value (view_of_ctx m.ctx) other))
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
       Reporter.fatalf
         ~loc
         Elab_error
         "Lambda checked against non-Pi: %s"
         (Pretty.pp_value (view_of_ctx m.ctx) ty))
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
        | Core.VPi ({ implicit; name = _; bound = a }, b) ->
          if is_implicit = implicit
          then begin
            push m (KApp_HaveArg (loc, f_tm, b));
            push m (GCheck (loc, arg, a))
          end
          else if implicit
          then begin
            (* Insert a fresh implicit meta on the f side, then retry. *)
            let meta_tm = Meta.meta_fresh m.ctx.lvl in
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
          Reporter.fatalf
            ~loc
            Type_error
            "cannot apply to `(%s) : %s`"
            (Pretty.pp_term (view_of_ctx m.ctx) f_tm)
            (Pretty.pp_value (view_of_ctx m.ctx) ty))
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
  | GInfer (loc, RecordLit _) ->
    Reporter.fatalf
      ~loc
      Elab_error
      "cannot infer the type of a record literal; please annotate"
  | GCheck (loc, RecordLit entries, expected_ty) ->
    (match Evaluation.force_head expected_ty with
     | Core.VRecordType { name = r_name; fields = type_fields; field_env; field_terms; _ }
       ->
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
         (Pretty.pp_value (view_of_ctx m.ctx) other))
  | KRecordLit_Field
      ( loc
      , r_name
      , done_rev
      , current_fname
      , remaining_entries
      , remaining_term_binders
      , eval_env ) ->
    (match take_result m with
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
        | (fname, expr) :: rest_entries, (t : Core.typ Syntax.binder) :: rest_term_types
          ->
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
       Reporter.fatalf
         Elab_error
         "KRecordLit_Field: bad result %s"
         ([%show: produced] other))
  | GInfer (loc, RecordUpdate _) ->
    Reporter.fatalf
      ~loc
      Elab_error
      "cannot infer the type of a record update; please annotate"
  | GCheck (loc, RecordUpdate (base, overrides), expected_ty) ->
    (match Evaluation.force_head expected_ty with
     | Core.VRecordType { name = r_name; fields = type_fields; field_env; field_terms; _ }
       ->
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
         (Pretty.pp_value (view_of_ctx m.ctx) other))
  | KRecordUpdate_HaveBase (loc, r_name, overrides, term_fields, field_env) ->
    (match take_result m with
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
         ([%show: produced] other))
  | KRecordUpdate_Field
      ( loc
      , r_name
      , base_core
      , overrides
      , done_rev
      , current_fname
      , remaining_term_fields
      , eval_env ) ->
    (match take_result m with
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
       Reporter.fatalf
         Elab_error
         "KRecordUpdate_Field: bad result %s"
         ([%show: produced] other))
  | GInfer (loc, Proj (e, f)) ->
    push m (KProj_HaveRec (loc, f));
    push m (GInfer (loc, e))
  | KProj_HaveRec (loc, f) ->
    (match take_result m with
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
                (Pretty.pp_value (view_of_ctx m.ctx) other)
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
            (Pretty.pp_value (view_of_ctx m.ctx) other))
     | other ->
       Reporter.fatalf Elab_error "KProj_HaveRec: bad result %s" ([%show: produced] other))
  | GInfer (loc, Lambda _) -> Reporter.fatalf ~loc Elab_error "cannot infer lambda term"
  | GCheck (_loc, Hole, _) -> m.result <- Some (PTerm (Meta.meta_fresh m.ctx.lvl))
  | GInfer (_loc, Hole) ->
    let ty = Evaluation.eval m.ctx.env (Meta.meta_fresh m.ctx.lvl) in
    let tm = Meta.meta_fresh m.ctx.lvl in
    m.result <- Some (PTermType (tm, ty))
  | GCheck (loc, Inline_elim d, ty) ->
    (match d.siblings with
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
            | Some (_, `Inductive info) -> Inductive.build_owner_map ~ind_head info
            | _ -> [])
         | _ -> []
       in
       let result_type_surface =
         Inductive.readback_value_to_surface ~loc ~user_level_names ~owner_map resolved_ty
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
       push m (GCheck (loc, expanded, ty)))
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
          let lhs = List.nth xs (List.length xs - 2) in
          let rhs = List.nth xs (List.length xs - 1) in
          (match Evaluation.force_head lhs, Evaluation.force_head rhs with
           | Core.Label (c1, _), Core.Label (c2, _) when not (String.equal c1 c2) ->
             let empty_ty = Core.IndType ("Empty", Bwd.Emp) in
             m.result <- Some (PTermType (Core.IdAbsurd p_tm, empty_ty))
           | l, r ->
             Reporter.fatalf
               ~loc
               Elab_error
               "\\absurd-id: expected Id of distinct-ctor-headed values, got `Id _ %s %s`"
               (Pretty.pp_value (view_of_ctx m.ctx) l)
               (Pretty.pp_value (view_of_ctx m.ctx) r))
        | other ->
          Reporter.fatalf
            ~loc
            Elab_error
            "\\absurd-id: argument is not Id-typed, got `%s`"
            (Pretty.pp_value (view_of_ctx m.ctx) other))
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
  | GTopUniverseDecl names ->
    List.iter Context.declare_level_var names;
    m.result <- Some PUnit
  | GTopLet (loc, name, bindings, result_ty, body) ->
    let typ : Surface.pretype =
      List.fold_right
        (fun binding return_ty -> Surface.Pi (binding, return_ty))
        bindings
        result_ty
    in
    push m (KTopLet_HaveType (loc, name, body, bindings));
    push m (GInferType (loc, typ))
  | KTopLet_HaveType (loc, name, body, bindings) ->
    (match take_result m with
     | PType (typ_tm, _) ->
       let typ_val = Evaluation.eval m.ctx.env typ_tm in
       let term : Surface.preterm =
         List.fold_right
           (fun { name; implicit; bound = _ } body ->
              Surface.Lambda { name; bound = body; implicit })
           bindings
           body
       in
       push m (KTopLet_HaveBody (loc, name, typ_tm, typ_val));
       push m (GCheck (loc, term, typ_val))
     | other ->
       Reporter.fatalf
         Elab_error
         "KTopLet_HaveType: bad result %s"
         ([%show: produced] other))
  | KTopLet_HaveBody (loc, name, typ_tm, typ_val) ->
    (match take_result m with
     | PTerm term ->
       let exported = m.is_exported name in
       publish_to_context ~exported [ name ] (typ_val, `Defn);
       let body_val = Evaluation.eval m.ctx.env term in
       publish_to_env ~exported [ name ] (body_val, `Defn);
       Env.register_definition name body_val;
       let qname = m.module_name ^ "." ^ name in
       (try Check.accept_let m.kernel_module ~name:qname ~ty:typ_tm ~body:term with
        | Violet_kernel.Error.Kernel_error err ->
          Reporter.fatalf
            ~loc
            Elab_error
            "kernel rejected `%s`: %s"
            qname
            (Violet_kernel.Error.show_kernel_error err));
       m.result <- Some PUnit
     | other ->
       Reporter.fatalf
         Elab_error
         "KTopLet_HaveBody: bad result %s"
         ([%show: produced] other))
  | GTopStackDef (loc, name, bindings, result_ty, moves, clauses) ->
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
    push m (KTopStackDef_HaveType (loc, name, bindings, result_ty, moves, clauses));
    push m (GInferType (loc, typ))
  | KTopStackDef_HaveType (loc, name, bindings, signature, moves, clauses) ->
    (match take_result m with
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
       push m (KTopLet_HaveBody (loc, name, typ_tm, typ_val));
       push m (GCheck (loc, term, typ_val))
     | other ->
       Reporter.fatalf
         Elab_error
         "KTopStackDef_HaveType: bad result %s"
         ([%show: produced] other))
  | GTopElimDef (loc, name, bindings, result_ty, opens, intros, target, clauses) ->
    let typ : Surface.pretype =
      List.fold_right
        (fun binding return_ty -> Surface.Pi (binding, return_ty))
        bindings
        result_ty
    in
    push
      m
      (KTopElimDef_HaveType
         (loc, name, bindings, result_ty, opens, intros, target, clauses));
    push m (GInferType (loc, typ))
  | KTopElimDef_HaveType (loc, name, bindings, signature, opens, intros, target, clauses)
    ->
    (match take_result m with
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
       (* Peel target_pos VPi binders off typ_val, substituting fresh
          rigid_local levels (matching the levels the elaborator will
          assign when it later checks the wrapping intro-lambdas). The
          target's type is then the bound of the next VPi. *)
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
       push m (KTopLet_HaveBody (loc, name, typ_tm, typ_val));
       push m (GCheck (loc, term, typ_val))
     | other ->
       Reporter.fatalf
         Elab_error
         "KTopElimDef_HaveType: bad result %s"
         ([%show: produced] other))
  | GTopData (loc, Surface.Data { name; params; deps; ind_ty; ctors }) ->
    let typ : Surface.pretype =
      List.fold_right
        (fun binding return_ty -> Surface.Pi (binding, return_ty))
        (params @ deps)
        ind_ty
    in
    push m (KTopData_HaveType (loc, name, params, deps, ind_ty, ctors));
    push m (GInferType (loc, typ))
  | KTopData_HaveType (loc, name, params, deps, ind_ty, ctors) ->
    (match take_result m with
     | PType (typ_tm, inferred_sort) ->
       let typ_val = Evaluation.eval m.ctx.env typ_tm in
       let rec final_sort_of_val (ctx_lvl : int) (v : Core.value) : Level.level =
         match Evaluation.force_head v with
         | Core.VPi (_, b) ->
           final_sort_of_val (ctx_lvl + 1) (b (Core.rigid_local ctx_lvl))
         | Core.Universe l -> l
         | other ->
           Reporter.fatalf
             ~loc
             Elab_error
             "data type `%s`'s spine should end in a Universe, got `%s`"
             name
             (Pretty.pp_value (view_of_ctx m.ctx) other)
       in
       let user_sort = final_sort_of_val m.ctx.lvl typ_val in
       if not (Level.le inferred_sort (Level.lsuc user_sort))
       then
         Reporter.fatalf
           ~loc
           Type_error
           "inductive type `%s`'s declared return sort `%s` is not large enough; \
            constructed Pi-tower lives at sort `%s`"
           name
           (Pretty.pp_level user_sort)
           (Pretty.pp_level inferred_sort);
       let lookup_polarity (n : string) : Context.polarity list option =
         match Context.S.resolve [ n ] with
         | Some (_, `Inductive info) -> Some (info : Context.ind_info).param_polarity
         | _ -> None
       in
       Positivity.check_strict_positivity
         ~loc:(Some loc)
         ~ind_name:name
         ~params
         ~deps
         ~lookup_polarity
         ctors;
       let param_polarity =
         Positivity.infer_param_polarity ~ind_name:name ~params ~lookup_polarity ctors
       in
       let infos =
         List.map (Eliminator_synth.analyze_ctor ~ind_name:name ~params) ctors
       in
       let ind_info : Context.ind_info =
         { params; deps; ind_ty; ctors; infos; param_polarity }
       in
       let exported = m.is_exported name in
       publish_to_context ~exported [ name ] (typ_val, `Inductive ind_info);
       publish_to_env ~exported [ name ] (Core.IndType (name, Bwd.Emp), `Constructor);
       let ctor_names =
         List.map (fun (b : Surface.pretype binder) -> Syntax.Name.to_string b.name) ctors
       in
       let qname = m.module_name ^ "." ^ name in
       let qctor_names =
         List.map (fun cn -> m.module_name ^ "." ^ name ^ "." ^ cn) ctor_names
       in
       Check.accept_data m.kernel_module ~name:qname ~ty:typ_tm ~ctor_names:qctor_names;
       List.iter
         (bind_constructor
            ~loc
            ~exported
            ~ind_name:name (* bare *)
            ~ind_qname:qname (* module.Nat for kernel *)
            ~module_name:m.module_name
            ~kernel_module:m.kernel_module
            m.ctx
            params)
         ctors;
       let elim_typ : Surface.pretype =
         Eliminator_synth.eliminator_type ~name ~params ~deps ~ind_ty ctors
       in
       let elim_name = "elim" in
       (* Two-segment path used for namespace resolution in the type context *)
       let elim_path = [ name; elim_name ] in
       let elim_flat = name ^ "/" ^ elim_name in
       let elim_typ_tm = check_type ~loc m.ctx elim_typ in
       let elim_typ_val = Evaluation.eval m.ctx.env elim_typ_tm in
       publish_to_context ~exported elim_path (elim_typ_val, `Eliminator);
       let reducer_label = elim_flat in
       let reducer =
         Eliminator_synth.build_elim_reducer
           ~ind_name:name
           ~elim_name:reducer_label
           ~params
           ~deps
           ctors
       in
       let elim_head : Core.elim_head = { elim_name = reducer_label; reducer } in
       let elim_value = Core.Elim (elim_head, Bwd.Emp) in
       (* Register in env under the flat key so kernel eval can find it *)
       publish_to_env ~exported [ elim_flat ] (elim_value, `Eliminator);
       let qelim_name = m.module_name ^ "." ^ name ^ "." ^ elim_name in
       Check.accept_elim
         m.kernel_module
         ~name:qelim_name
         ~ty:elim_typ_tm
         ~reducer:elim_head;
       if
         false
         && params = []
         && deps = []
         && Context.has "Id"
         && Context.has "subst"
         && Context.has "Empty"
         && Context.has "Sigma"
       then (
         let publish_def nc_name nc_typ_tm nc_typ_val nc_body_tm nc_body_val =
           publish_to_context ~exported [ nc_name ] (nc_typ_val, `Defn);
           publish_to_context ~exported [ name; nc_name ] (nc_typ_val, `Defn);
           let nc_flat = name ^ "/" ^ nc_name in
           publish_to_env ~exported [ nc_flat ] (nc_body_val, `Defn);
           Env.register_definition nc_flat nc_body_val;
           let qnc_name = m.module_name ^ "." ^ name ^ "." ^ nc_name in
           Check.accept_let m.kernel_module ~name:qnc_name ~ty:nc_typ_tm ~body:nc_body_tm
         in
         let nct_typ, nct_body = Eliminator_synth.no_confusion_type_def ~name ~ctors in
         let nct_typ_tm = check_type ~loc m.ctx nct_typ in
         let nct_typ_val = Evaluation.eval m.ctx.env nct_typ_tm in
         let nct_body_tm = check_term_against ~loc m.ctx nct_body nct_typ_val in
         let nct_body_val = Evaluation.eval m.ctx.env nct_body_tm in
         publish_def "no-confusion-type" nct_typ_tm nct_typ_val nct_body_tm nct_body_val;
         let nc_typ, nc_body = Eliminator_synth.no_confusion_def ~name ~ctors in
         let nc_typ_tm = check_type ~loc m.ctx nc_typ in
         let nc_typ_val = Evaluation.eval m.ctx.env nc_typ_tm in
         let nc_body_tm = check_term_against ~loc m.ctx nc_body nc_typ_val in
         let nc_body_val = Evaluation.eval m.ctx.env nc_body_tm in
         publish_def "no-confusion" nc_typ_tm nc_typ_val nc_body_tm nc_body_val);
       m.result <- Some PUnit
     | other ->
       Reporter.fatalf
         Elab_error
         "KTopData_HaveType: bad result %s"
         ([%show: produced] other))
  | GTopData (_, _) -> Reporter.fatalf Elab_error "GTopData: payload is not Data"
  | GTopRecord (loc, Surface.Record { name; params; ind_ty; fields }) ->
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
  | GTopRecord (_, _) -> Reporter.fatalf Elab_error "GTopRecord: payload is not Record"
  | KTopRecord_HaveType (loc, name, params, ind_ty, fields) ->
    (match take_result m with
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
         let param_vars =
           List.init n_params (fun i -> Core.LocalVar (n_params - 1 - i))
         in
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
       Check.accept_let m.kernel_module ~name:qname ~ty:typ_tm ~body:head_body;
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
         List.fold_left
           (fun f i -> Core.App (f, Core.LocalVar (depth_extra + n_params - 1 - i)))
           base
           (List.init n_params (fun i -> i))
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
             (fun i fname ->
                Syntax.Name.to_string fname, Core.LocalVar (n_fields - 1 - i))
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
       (* Also register under two-segment path [name; "mk"] so that surface
          syntax `R/mk` (parsed as Var [R; "mk"]) can resolve the companion. *)
       publish_to_context ~exported [ name; "mk" ] (mk_ty_val, `Defn);
       let mk_body_val = Evaluation.eval m.ctx.env mk_body in
       publish_to_env ~exported [ mk_name ] (mk_body_val, `Defn);
       Env.register_definition mk_name mk_body_val;
       let q_mk_name = m.module_name ^ "." ^ mk_name in
       Check.accept_let m.kernel_module ~name:q_mk_name ~ty:mk_ty ~body:mk_body;
       (* --- R/fᵢ companions ---
          For each field fᵢ (0-indexed):
          ty  = Pi(P₁:Q₁,...,Pi(Pₖ:Qₖ, Pi(r:R_applied, Tᵢ_projected)))
          body = Lambda(P₁,...,Lambda(Pₖ, Lambda(r, RecordProj { record=LocalVar 0; field=fᵢ })))

          Tᵢ_projected: substitute in Tᵢ_tm (depth k+i context):
            - LocalVar j for j in [0..i-1] (prev fields) ->
                RecordProj { record = LocalVar(depth_extra + k - j); field = prev_field }
                where in the projection type under 1 extra binder (r), depth_extra=0 outside + 0 Pi walk,
                but actually we're at depth k+1 total with r=ix 0, Pₖ=ix 1, ..., P₁=ix k.
                So in Tᵢ_projected (depth k+1 binders): r=ix 0.
                field fⱼ (0-indexed, j < i) was at LocalVar (i-1-j) in Tᵢ_tm.
                Replace with RecordProj { record=LocalVar 0; field=field_names[j] }
                ... but LocalVar 0 refers to r, which is CORRECT only at depth 0 in Tᵢ_projected.
                We need a shifting substitution as we go deeper.
            - LocalVar j for j in [i..i+k-1] (params) -> LocalVar(j - i + 1)
              (was param at offset i+j', now at offset 1+j' in the proj type)
       *)
       let subst_proj_result_ty
             ~(n_before : int)
             ~(n_params_here : int)
             ~(prev_field_names : string list)
             (tm : Core.term)
         : Core.term
         =
         (* Perform a substitution with depth tracking.
            At extra_depth (additional binders descended into during walk),
            the occurrences of LocalVar shift:
            - LocalVar (j + extra_depth) for j in [0..n_before-1] (shifted field refs)
              -> RecordProj { record=LocalVar(extra_depth); field=prev_field_names[n_before-1-j] }
              (r is at LocalVar extra_depth when extra_depth more binders surround us)
            - LocalVar (j + extra_depth) for j in [n_before..n_before+n_params_here-1] (param refs)
              -> LocalVar(j - n_before + 1 + extra_depth)
            - LocalVar (j + extra_depth) for j < 0: impossible (extra_depth accounts for new binders)
         *)
         let rec go extra_depth t =
           match t with
           | Core.LocalVar ix ->
             let j = ix - extra_depth in
             if j >= 0 && j < n_before
             then
               (* field reference: replace with projection on r (at extra_depth below us) *)
               Core.RecordProj
                 { record = Core.LocalVar extra_depth
                 ; field = List.nth prev_field_names (n_before - 1 - j)
                 }
             else if j >= n_before && j < n_before + n_params_here
             then
               (* param reference: shift down by n_before - 1 *)
               Core.LocalVar (ix - n_before + 1)
             else
               (* deeper local or something else: shift down to account for lost field binders,
                  but add 1 for the new r binder *)
               Core.LocalVar (ix - n_before + 1)
           | Core.Universe _ -> t
           | Core.Var _ -> t
           | Core.App (a, b) -> Core.App (go extra_depth a, go extra_depth b)
           | Core.Lambda { name; bound; implicit } ->
             Core.Lambda { name; bound = go (extra_depth + 1) bound; implicit }
           | Core.TypedLambda ({ name; bound = dom; implicit }, body) ->
             Core.TypedLambda
               ({ name; bound = go extra_depth dom; implicit }, go (extra_depth + 1) body)
           | Core.Pi ({ name; bound = dom; implicit }, cod) ->
             Core.Pi
               ({ name; bound = go extra_depth dom; implicit }, go (extra_depth + 1) cod)
           | Core.Meta _ | Core.InsertedMeta _ -> t
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
              subst_proj_result_ty
                ~n_before:i
                ~n_params_here:n_params
                ~prev_field_names
                field_core_tys.(i)
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
            Check.accept_let m.kernel_module ~name:q_proj_name ~ty:proj_ty ~body:proj_body)
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
                  Core.App (f, Core.LocalVar (n_params + n_fields + 1 - i)))
               (Core.Var mk_name)
               (List.init n_params (fun i -> i))
           in
           List.fold_left
             (fun f i ->
                (* fᵢ (0-indexed, f₁ first) = ix(n_fields-1-i) under k+2+n binders *)
                Core.App (f, Core.LocalVar (n_fields - 1 - i)))
             with_params
             (List.init n_fields (fun i -> i))
         in
         let m_applied = Core.App (Core.LocalVar n_fields, mk_full_applied) in
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
         let m_r = Core.App (Core.LocalVar 1, Core.LocalVar 2) in
         let case_pi =
           Core.Pi ({ name = Named "case"; bound = case_ty_tm; implicit = false }, m_r)
         in
         let m_pi =
           Core.Pi ({ name = Named "M"; bound = motive_ty_tm; implicit = false }, case_pi)
         in
         let r_pi =
           Core.Pi
             ({ name = Named "r"; bound = rec_applied_under 0; implicit = false }, m_pi)
         in
         wrap_param_pis r_pi
       in
       (* Under k+3 binders: case=ix 0, M=ix 1, r=ix 2. *)
       let elim_body : Core.term =
         let r_var = Core.LocalVar 2 in
         let projections =
           List.map
             (fun fn ->
                Core.RecordProj { record = r_var; field = Syntax.Name.to_string fn })
             field_names
         in
         let inner =
           List.fold_left (fun f arg -> Core.App (f, arg)) (Core.LocalVar 0) projections
         in
         let with_case =
           Core.Lambda { name = Named "case"; bound = inner; implicit = false }
         in
         let with_m =
           Core.Lambda { name = Named "M"; bound = with_case; implicit = false }
         in
         let with_r =
           Core.Lambda { name = Named "r"; bound = with_m; implicit = false }
         in
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
       Check.accept_let m.kernel_module ~name:q_elim_name ~ty:elim_ty ~body:elim_body;
       m.result <- Some PUnit
     | other ->
       Reporter.fatalf
         Elab_error
         "KTopRecord_HaveType: bad result %s"
         ([%show: produced] other))

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

and bind_constructor
      ~loc
      ~exported
      ~(ind_name : string)
      (* bare inductive name for surface scope *)
      ~(ind_qname : string)
      (* module-qualified for kernel *)
      ~(module_name : string)
      ~(kernel_module : Violet_kernel.Module.t)
      (ctx : local_ctx)
      (params : Surface.pretype binder list)
      ({ name; bound = typ; _ } : Surface.pretype binder)
  : unit
  =
  let name = Syntax.Name.to_string name in
  let typ = Inductive.close_ctor_type params typ in
  let ctor_ty_tm = check_type ~loc ctx typ in
  let ctor_ty = Evaluation.eval ctx.env ctor_ty_tm in
  let ctor_flat = ind_name ^ "/" ^ name in
  (* Context: multi-segment for type-directed surface resolution *)
  publish_to_context ~exported [ ind_name; name ] (ctor_ty, `Constructor);
  (* Env: flat key matching the kernel's E.lookup string.
     The Label value carries the BARE name so the eliminator reducer's
     find_ctor_index (which compares against info.ctor_name = bare name) works. *)
  publish_to_env ~exported [ ctor_flat ] (Core.Label (name, Bwd.Emp), `Constructor);
  (* Also register under the bare name so that the unifier's rename/eval
     round-trip (Label x -> Var x -> eval -> lookup x) still finds Label x. *)
  publish_to_env ~exported [ name ] (Core.Label (name, Bwd.Emp), `Constructor);
  let qctor_name = module_name ^ "." ^ ind_name ^ "." ^ name in
  Check.accept_ctor kernel_module ~name:qctor_name ~data:ind_qname ~ty:ctor_ty_tm
;;

let with_handlers (k : unit -> 'a) : 'a =
  Reporter.run
    ~emit:(fun _ -> ())
    ~fatal:(fun d -> failwith ([%show: Reporter.Message.t] d.message))
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
    | Surface.Let (name, bindings, result_ty, body) ->
      GTopLet (loc, name, bindings, result_ty, body)
    | Surface.Data _ as d -> GTopData (loc, d)
    | Surface.Stack_def { name; params; signature; moves; clauses } ->
      GTopStackDef (loc, name, params, signature, moves, clauses)
    | Surface.Elim_def { name; params; signature; opens; intros; target; clauses } ->
      GTopElimDef (loc, name, params, signature, opens, intros, target, clauses)
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

let check_module ?module_path (file : Surface.t) : unit =
  let module_path =
    match module_path with
    | Some p -> p
    | None -> [ Filename.chop_extension @@ Filename.basename file.name ]
  in
  let module_name = String.concat "/" module_path in
  (* Run the operator-resolution pass first. It walks every preterm and
     rewrites Op_soup nodes into normal App / Var spines using the in-scope
     operator table. With no `operator` declarations, this is a structural
     no-op that just collapses each soup to a left-associative App. *)
  let file = Op_resolver.resolve_module ~module_name file in
  Eio.traceln "checking [module] %s (%s)" module_name file.name;
  let kernel_module = Violet_kernel.Module.create () in
  Context.clear_level_vars ();
  let has_explicit_universe_decl =
    List.exists
      (fun (top : Surface.top Asai.Range.located) ->
         match top.value with
         | Surface.Universe_decl _ -> true
         | _ -> false)
      file.tops
  in
  if not has_explicit_universe_decl then Context.declare_level_var "U";
  let exports_set =
    let h = Hashtbl.create 16 in
    List.iter (fun n -> Hashtbl.replace h n ()) file.exports;
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
  List.iter
    (fun (top : Surface.top Asai.Range.located) ->
       let loc = Option.get top.loc in
       check_top ~module_name ~kernel_module ~goal_counter ~is_exported ~loc top.value)
    file.tops;
  let bound_names : (string, unit) Hashtbl.t = Hashtbl.create 16 in
  Yuujinchou.Trie.iter
    (fun path _ ->
       match Bwd.to_list path with
       | [] -> ()
       | seg :: _ -> Hashtbl.replace bound_names seg ())
    (Context.S.get_export ());
  let undefined = List.filter (fun n -> not (Hashtbl.mem bound_names n)) file.exports in
  match undefined with
  | [] -> ()
  | names ->
    Reporter.fatalf
      Export_error
      "the following names are listed in \\export but never defined: %s"
      (String.concat ", " names)
;;

(* REPL helpers. These run a single GInfer against an existing handler state
   (Context.S / Env.S already populated by prior `check_module` calls).
   The caller is responsible for entering the right `Context.S.section` /
   `Env.S.section` and re-applying any visible-namespace imports so that the
   expression sees the names it expects. *)

let infer_expression ~(module_name : string) (p : Surface.preterm)
  : Core.term * Core.value
  =
  let loc =
    match loc_of p with
    | Some l -> l
    | None -> Asai.Range.of_lex_range (Lexing.dummy_pos, Lexing.dummy_pos)
  in
  let m =
    make_machine
      ~module_name
      ~kernel_module:(Violet_kernel.Module.create ())
      ~goal_counter:(ref 0)
      ()
  in
  push m (GInfer (loc, p));
  match drive m with
  | PTermType (tm, ty) -> tm, ty
  | other ->
    Reporter.fatalf ~loc Elab_error "infer_expression: got %s" ([%show: produced] other)
;;

let normalize_term (tm : Core.term) : Core.value = Evaluation.eval Bwd.Emp tm

(* User-facing pretty-printer for REPL output. The empty local context is fine
   because expressions typed at the REPL don't introduce free locals — every
   surface name resolves against the global scope. *)
let pretty_repl_value (v : Core.value) : string = Pretty.pp_value Context_view.empty v

let%expect_test "type-directed: bare zero against Nat resolves to Nat/zero" =
  let dummy_loc = Asai.Range.of_lex_range (Lexing.dummy_pos, Lexing.dummy_pos) in
  let loc top = Asai.Range.locate dummy_loc top in
  let nat_data : Surface.top =
    Surface.Data
      { name = "Nat"
      ; params = []
      ; deps = []
      ; ind_ty = Surface.Universe
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
      }
  in
  let let_zero : Surface.top =
    Surface.Let ("x", [], Surface.Var [ "Nat" ], Surface.Var [ "zero" ])
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
      ( "foo"
      , []
      , Surface.Pi
          ( { Syntax.name = Named "x"; bound = Surface.Universe; implicit = false }
          , Surface.Universe )
      , Surface.Lambda
          { Syntax.name = Named "x"; bound = Surface.Var [ "x" ]; implicit = false } )
  in
  (* uses_foo : (x : U) -> U => foo  — alias for foo; typechecks iff foo is visible *)
  let uses_foo_def =
    Surface.Let
      ( "uses_foo"
      , []
      , Surface.Pi
          ( { Syntax.name = Named "x"; bound = Surface.Universe; implicit = false }
          , Surface.Universe )
      , Surface.Var [ "foo" ] )
  in
  let mod_a : Surface.t =
    { name = "a.vt"; imports = []; exports = []; tops = [ loc foo_def ] }
  in
  let mod_b : Surface.t =
    { name = "b.vt"; imports = [ [ "a" ] ]; exports = []; tops = [ loc uses_foo_def ] }
  in
  (try
     with_handlers (fun () ->
       check_module mod_a;
       check_module mod_b);
     print_endline "UNEXPECTED: importer saw private name"
   with
   | _ -> print_endline "rejected as expected (foo is private)");
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
    rejected as expected (foo is private)
    |}]
;;

let%expect_test "module: \\export-listed let is visible to importers" =
  let dummy_loc = Asai.Range.of_lex_range (Lexing.dummy_pos, Lexing.dummy_pos) in
  let loc top = Asai.Range.locate dummy_loc top in
  (* foo : (x : U) -> U => fun x -> x  — well-typed identity on U *)
  let foo_def =
    Surface.Let
      ( "foo"
      , []
      , Surface.Pi
          ( { Syntax.name = Named "x"; bound = Surface.Universe; implicit = false }
          , Surface.Universe )
      , Surface.Lambda
          { Syntax.name = Named "x"; bound = Surface.Var [ "x" ]; implicit = false } )
  in
  (* uses_foo : (x : U) -> U => foo  — alias for foo; typechecks iff foo is visible *)
  let uses_foo_def =
    Surface.Let
      ( "uses_foo"
      , []
      , Surface.Pi
          ( { Syntax.name = Named "x"; bound = Surface.Universe; implicit = false }
          , Surface.Universe )
      , Surface.Var [ "foo" ] )
  in
  let mod_a : Surface.t =
    { name = "a.vt"; imports = []; exports = [ "foo" ]; tops = [ loc foo_def ] }
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
    { name = "a.vt"; imports = []; exports = [ "ghost" ]; tops = [] }
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
      ; params = []
      ; deps = []
      ; ind_ty = Surface.Universe
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
      }
  in
  let mod_a : Surface.t =
    { name = "a.vt"; imports = []; exports = [ "Nat" ]; tops = [ loc nat_data ] }
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
               ("uses_bundle", [], Surface.Var [ "Nat" ], Surface.Var [ "Nat"; "zero" ]))
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
      ; params = []
      ; deps = []
      ; ind_ty = Surface.Universe
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
      }
  in
  let point_record : Surface.top =
    Surface.Record
      { name = "Point"
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
    ; exports = [ "Nat"; "Point" ]
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
               ( "uses_proj"
               , []
               , Surface.Pi
                   ( { name = Anon; bound = Surface.Var [ "Point" ]; implicit = false }
                   , Surface.Var [ "Nat" ] )
               , Surface.Var [ "Point/x" ] ))
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
      ; params = []
      ; deps = []
      ; ind_ty = Surface.Universe
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
      }
  in
  let point_record : Surface.top =
    Surface.Record
      { name = "Point"
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
      ; params = []
      ; deps = []
      ; ind_ty = Surface.Universe
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
      }
  in
  let pair_record : Surface.top =
    Surface.Record
      { name = "Pair"
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
      ( "p"
      , []
      , Surface.App
          ( false
          , Surface.App (false, Surface.Var [ "Pair" ], Surface.Var [ "Nat" ])
          , Surface.Var [ "Nat" ] )
      , Surface.RecordLit
          [ "fst", Surface.Var [ "Nat"; "zero" ]; "snd", Surface.Var [ "Nat"; "zero" ] ]
      )
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
      ; params = []
      ; deps = []
      ; ind_ty = Surface.Universe
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
      }
  in
  let pair_record : Surface.top =
    Surface.Record
      { name = "Pair"
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
      ( "p"
      , []
      , Surface.App
          ( false
          , Surface.App (false, Surface.Var [ "Pair" ], Surface.Var [ "Nat" ])
          , Surface.Var [ "Nat" ] )
      , Surface.RecordLit [ "fst", Surface.Var [ "Nat"; "zero" ] ] )
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
