open Violet_surface
open Violet_common
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

(* local_ctx tracks:
   - env:   values for de Bruijn indexing during eval
   - types: types of the same locals, for type-checking lookup
   - names: surface names of the same locals, for surface→core resolution
   - lvl:   current de Bruijn level (= Bwd.length env), threaded for fresh metas
   All four grow together — `extend` keeps them in sync. *)
type local_ctx =
  { env : Core.value bwd
  ; types : Core.value bwd
  ; names : Syntax.binder_name Surface.spanned bwd
  ; lvl : int
  }

let empty_ctx : local_ctx = { env = Emp; types = Emp; names = Emp; lvl = 0 }

let extend
      (ctx : local_ctx)
      (name : Syntax.binder_name Surface.spanned)
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
  Context_view.make
    ~names:(Bwd.map (fun n -> Syntax.Name.to_string n.Surface.value) ctx.names)
    ~lvl:ctx.lvl
;;

let bind (ctx : local_ctx) (name : Syntax.binder_name Surface.spanned) (ty : Core.value)
  : local_ctx
  =
  extend ctx name ty (Core.RigidLocal (ctx.lvl, Emp))
;;

(* Look up a surface name in the local context.  Returns the de Bruijn INDEX
   (innermost = 0) if found, or None if it's a global. `Anon` binders carry
   no string name, so they never match. *)
let resolve_local (ctx : local_ctx) (x : string) : int option =
  let rec go i = function
    | Emp -> None
    | Snoc (_, { Surface.value = Syntax.Named n; _ }) when String.equal n x -> Some i
    | Snoc (rest, _) -> go (i + 1) rest
  in
  go 0 ctx.names
;;

(* The source span of the local binder at de Bruijn INDEX [ix]. Same nth walk
   as [local_type] but over [names], returning the binder's own [.loc]. *)
let local_binder_loc (ctx : local_ctx) (ix : int) : Asai.Range.t =
  let rec nth (env : Syntax.binder_name Surface.spanned bwd) i =
    match env, i with
    | Snoc (_, n), 0 -> n.Surface.loc
    | Snoc (rest, _), k -> nth rest (k - 1)
    | Emp, _ -> Reporter.fatalf Elab_error "local index %d out of range in names" ix
  in
  nth ctx.names ix
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
     | Some { Surface.pnode = Surface.PVar v; _ } -> v
     | _ -> Printf.sprintf "__x%d" position)
;;

type produced =
  | PTerm of Core.term
  | PTermType of Core.term * Core.value_ty
  | PType of Core.term * Level.level
  | PUnit

(* The constructor tag of a [produced]. Used only in "bad result" invariant
   panics, where the offending shape (not its contents) is what matters. *)
let produced_tag : produced -> string = function
  | PTerm _ -> "PTerm"
  | PTermType _ -> "PTermType"
  | PType _ -> "PType"
  | PUnit -> "PUnit"
;;

type goal =
  | GCheck of Surface.preterm * Core.value_ty
  | GInfer of Surface.preterm
  | GInferType of Surface.pretype
  | KCheckBy_Infer of t * Core.value_ty
  | KApp_HaveFn of t * bool * Surface.preterm
  | KApp_HaveArg of t * Core.term * (Core.value -> Core.value) * bool
  | KPi_HaveDom of t * Syntax.binder_name Surface.spanned * bool * Surface.pretype
  | KPi_HaveCod of t * Syntax.binder_name * bool * Core.term * Level.level
  | KLam_Body of t * Syntax.binder_name * bool
  | KTypedLam_HaveDom of t * Syntax.binder_name Surface.spanned * bool * Surface.preterm
  | KTypedLam_HaveBody of t * Syntax.binder_name * bool * Core.term * Core.value_ty
  | KMax_HaveLeft of t * Surface.preterm
  | KMax_HaveRight of t * Level.level
  | KEnsureUniverse of t
  | KIdAbsurd_HaveArg of t
  | KAbsurd_HaveArg of t
  | GTopLet of
      { loc : t
      ; name : string Surface.spanned
      ; bindings : Surface.pretype Surface.sbinder list
      ; result_ty : Surface.pretype
      ; body : Surface.preterm
      }
  | GTopData of t * Surface.top
  | GTopUniverseDecl of string Surface.spanned list
  | GTopStackDef of
      { loc : t
      ; name : string Surface.spanned
      ; bindings : Surface.pretype Surface.sbinder list
      ; result_ty : Surface.pretype
      ; moves : Surface.stack_move list
      ; clauses : Surface.clause list
      }
  | KTopLet_HaveType of
      { loc : t
      ; name : string Surface.spanned
      ; body : Surface.preterm
      ; bindings : Surface.pretype Surface.sbinder list
      }
  | KTopLet_HaveBody of
      { loc : t
      ; name : string Surface.spanned
      ; typ_tm : Core.term
      ; typ_val : Core.value_ty
      }
  | GTopAxiom of
      { loc : t
      ; name : string Surface.spanned
      ; bindings : Surface.pretype Surface.sbinder list
      ; result_ty : Surface.pretype
      }
  | KTopAxiom_HaveType of
      { loc : t
      ; name : string Surface.spanned
      }
  | KTopElimDef_HaveBody of
      { loc : t
      ; name : string Surface.spanned
      ; typ_tm : Core.term
      ; typ_val : Core.value_ty
      ; func_name : string
      ; target_pos : int
      }
  | KTopData_HaveType of
      { loc : t
      ; name : string Surface.spanned
      ; params : Surface.pretype Surface.sbinder list
      ; deps : Surface.pretype Surface.sbinder list
      ; ind_ty : Surface.pretype
      ; ctors : Surface.pretype Surface.sbinder list
      }
  | KTopStackDef_HaveType of
      { loc : t
      ; name : string Surface.spanned
      ; bindings : Surface.pretype Surface.sbinder list
      ; signature : Surface.pretype
      ; moves : Surface.stack_move list
      ; clauses : Surface.clause list
      }
  | GTopElimDef of
      { loc : t
      ; name : string Surface.spanned
      ; bindings : Surface.pretype Surface.sbinder list
      ; result_ty : Surface.pretype
      ; opens : string list
      ; intros : (string Surface.spanned * bool) list
      ; target : string Surface.spanned
      ; clauses : Surface.clause list
      }
  | KTopElimDef_HaveType of
      { loc : t
      ; name : string Surface.spanned
      ; bindings : Surface.pretype Surface.sbinder list
      ; signature : Surface.pretype
      ; opens : string list
      ; intros : (string Surface.spanned * bool) list
      ; target : string Surface.spanned
      ; clauses : Surface.clause list
      }
  | GTopRecord of t * Surface.top
  | KTopRecord_HaveType of
      t
      * string
      * Surface.pretype Surface.sbinder list
      * Surface.pretype
      * Surface.pretype Surface.sbinder list
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
      * (string Surface.spanned * Surface.preterm) list
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
      * (string Surface.spanned * Surface.preterm) list
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
      * (string Surface.spanned * Surface.preterm) list
      * (string * Core.term) list
      * string
      * Core.typ Syntax.binder list
      * Core.value bwd

type deferred_goal =
  { dg_loc : Asai.Range.t
  ; dg_name : string
  ; dg_ctx : local_ctx
  ; dg_target : Core.value
  }

type machine =
  { mutable goals : goal list
  ; mutable result : produced option
  ; mutable ctx : local_ctx
  ; mutable saved_ctx : local_ctx list
  ; mutable deferred_goal_reports : deferred_goal list
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
  ; deferred_goal_reports = []
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
  m.deferred_goal_reports
  <- { dg_loc = loc; dg_name = name; dg_ctx = m.ctx; dg_target = target }
     :: m.deferred_goal_reports
;;

let render_goal_report ~(module_name : string) ?(def_name = "") (g : deferred_goal) : unit
  =
  let { dg_loc = loc; dg_name = name; dg_ctx = ctx; dg_target = target } = g in
  let buf = Buffer.create 128 in
  Buffer.add_string buf (Printf.sprintf "%s/?%s\n" module_name name);
  (match Axiom_deps.display_deps_of [ def_name ] with
   | [] -> ()
   | deps ->
     Buffer.add_string
       buf
       (Printf.sprintf
          "  --- axioms: %s ---\n"
          (String.concat ", " (List.map Syntax.Name.of_segments deps))));
  Buffer.add_string buf "  --- context ---\n";
  (* Bwd.to_list returns outermost-first. *)
  let names =
    List.map (fun n -> Syntax.Name.to_string n.Surface.value) (Bwd.to_list ctx.names)
  in
  let types = Bwd.to_list ctx.types in
  let pp_ctx =
    List.map2
      (fun n ty ->
         let pp_ty = Notation.pp_term (view_of_ctx ctx) (Evaluation.quote ctx.lvl ty) in
         n, pp_ty)
      names
      types
  in
  List.iter
    (fun (n, pp_ty) -> Buffer.add_string buf (Printf.sprintf "  %s : %s\n" n pp_ty))
    pp_ctx;
  let pp_target = Notation.pp_term (view_of_ctx ctx) (Evaluation.quote ctx.lvl target) in
  Observer.emit (Goal { path = [ name ]; loc; ty = target; ctx = pp_ctx; pp_target });
  Buffer.add_string buf "  --- target ---\n";
  Buffer.add_string buf (Printf.sprintf "  %s" pp_target);
  Reporter.emitf ~loc Goal_report "%s" (Buffer.contents buf)
;;

let flush_goal_reports ?(def_name = "") (m : machine) : unit =
  List.iter
    (render_goal_report ~module_name:m.module_name ~def_name)
    (List.rev m.deferred_goal_reports);
  m.deferred_goal_reports <- []
;;

let name_of_top : Surface.top -> string = function
  | Surface.Let { name; _ } -> name.Surface.value
  | Surface.Data { name; _ } -> name.Surface.value
  | Surface.Stack_def { name; _ } -> name.Surface.value
  | Surface.Elim_def { name; _ } -> name.Surface.value
  | Surface.Universe_decl _ -> "<universe_decl>"
  | Surface.Operator_decl _ -> "<operator_decl>"
  | Surface.Record { name; _ } -> name.Surface.value
  | Surface.Axiom { name; _ } -> name.Surface.value
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

(* Is this core head name a registered eliminator in the current scope?
   Used to gate Notation.register_fold at definition time. *)
let is_elim_head (en : string) : bool =
  match Context.S.resolve (Syntax.Name.to_segments en) with
  | Some (_, `Eliminator) -> true
  | _ -> false
;;

(* Shift all free LocalVar indices in a Core.term by `n`.
   Variables with index < cutoff (bound by binders we're inside) are left alone.
   This is the standard weakening operation for de Bruijn terms. *)
let rec shift_term ?(cutoff = 0) (n : int) (t : Core.term) : Core.term =
  match t with
  | Core.LocalVar ix -> if ix >= cutoff then Core.LocalVar (ix + n) else t
  | Core.Universe _ | Core.Var _ | Core.Meta _ | Core.InsertedMeta _ -> t
  | Core.App (a, b, implicit) ->
    Core.App (shift_term ~cutoff n a, shift_term ~cutoff n b, implicit)
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
  | Core.Empty -> Core.Empty
  | Core.Absurd t -> Core.Absurd (shift_term ~cutoff n t)
;;
