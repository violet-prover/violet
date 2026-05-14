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
  ; names : string bwd
  ; lvl : int
  }

let empty_ctx : local_ctx = { env = Emp; types = Emp; names = Emp; lvl = 0 }

let extend (ctx : local_ctx) (name : string) (ty : Core.value) (value : Core.value)
  : local_ctx
  =
  { env = Bwd.Snoc (ctx.env, value)
  ; types = Bwd.Snoc (ctx.types, ty)
  ; names = Bwd.Snoc (ctx.names, name)
  ; lvl = ctx.lvl + 1
  }
;;

(* `bind` is the common case: pushing a new binder.  The value placeholder is
   a fresh RigidLocal at the current level. *)
let bind (ctx : local_ctx) (name : string) (ty : Core.value) : local_ctx =
  extend ctx name ty (Core.RigidLocal (ctx.lvl, Emp))
;;

(* Look up a surface name in the local context.  Returns the de Bruijn INDEX
   (innermost = 0) if found, or None if it's a global. *)
let resolve_local (ctx : local_ctx) (x : string) : int option =
  let rec go i = function
    | Emp -> None
    | Snoc (rest, n) -> if String.equal n x then Some i else go (i + 1) rest
  in
  go 0 ctx.names
;;

(* Resolve a surface identifier that might refer to a declared universe
   variable.  Returns Some level if the name is a level var, else None. *)
let resolve_universe_var (x : string) : Level.level option =
  if Context.is_level_var x then Some (Level.LVar x) else None
;;

(* Look up the type of a local by index, mirroring resolve_local. *)
let local_type (ctx : local_ctx) (ix : int) : Core.value =
  let rec nth env i =
    match env, i with
    | Snoc (_, v), 0 -> v
    | Snoc (rest, _), k -> nth rest (k - 1)
    | Emp, _ -> Reporter.fatalf Elab_error "local index %d out of range in types" ix
  in
  nth ctx.types ix
;;

(* Wrap a constructor's user-written type with implicit Π over the inductive
   type's params, so the stored global type is self-contained and so the
   params are in scope while checking the user's constructor type. *)
let close_ctor_type (params : Surface.pretype binder list) (typ : Surface.pretype)
  : Surface.pretype
  =
  List.fold_right
    (fun param result -> Surface.Pi ({ param with implicit = true }, result))
    params
    typ
;;

(* Helpers for stack-style (Pterodactyl) definitions. *)

(* Pick a binder name for the LHS pattern position. If the first clause has a
   PVar at that position, reuse it; otherwise (e.g. PCon at a split site)
   synthesize a fresh name. *)
let pick_binder_name (clauses : Surface.clause list) (position : int) : string =
  match clauses with
  | [] -> Printf.sprintf "__x%d" position
  | { patterns; _ } :: _ ->
    (match List.nth_opt patterns position with
     | Some (Surface.PVar v) -> v
     | _ -> Printf.sprintf "__x%d" position)
;;

(* Peel `length bindings` Pi-layers off `typ_val`, extending ctx with the
   user-supplied param names and types. Returns the inner ctx and the goal
   value after all params are consumed. *)
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
         ([%show: Core.value] other))
;;

(* Best location for a Surface preterm — peels through `Located` wrappers to
   find the innermost recorded range. Returns `None` when no wrapper is
   present (e.g. for terms synthesized by the elaborator). *)
let rec loc_of : Surface.preterm -> Asai.Range.t option = function
  | Surface.Located { loc; value } ->
    (match loc_of value with
     | Some _ as inner -> inner
     | None -> loc)
  | _ -> None
;;

(* Peel `n` outer Pi-layers off a Surface pretype, returning the codomain. *)
let rec peel_pi_surface ~(loc : Asai.Range.t) (n : int) (s : Surface.pretype)
  : Surface.pretype
  =
  if n = 0
  then s
  else (
    match s with
    | Surface.Located { value; loc = inner } ->
      peel_pi_surface ~loc:(Option.value inner ~default:loc) n value
    | Surface.Pi (_, cod) -> peel_pi_surface ~loc (n - 1) cod
    | _ ->
      Reporter.fatalf
        ~loc
        Elab_error
        "stack-def: signature has fewer Pi-layers than required (%d remaining)"
        n)
;;

(* In a clause body, rewrite calls to the function being defined where the
   target-position argument is a recursive case-arg, replacing the call with
   the corresponding IH applied to the trailing args. Errors on non-structural
   recursive calls (target-position arg is not a recursive case-arg). *)
let rewrite_recursive_calls
      ~(loc : Asai.Range.t)
      ~(func_name : string)
      ~(arity : int)
      ~(target_pos : int)
      ~(rec_arg_to_ih : (string * string) list)
      (body : Surface.preterm)
  : Surface.preterm
  =
  let rec spine_of acc = function
    | Surface.App (impl, f, a) -> spine_of ((impl, a) :: acc) f
    | Surface.Located { value = t; _ } -> spine_of acc t
    | head -> head, acc
  in
  let rec strip = function
    | Surface.Located { value = t; _ } -> strip t
    | t -> t
  in
  let rec rw t =
    match t with
    | Surface.Located { value = inner; loc } -> Surface.Located { value = rw inner; loc }
    | Surface.App _ ->
      let here = Option.value (loc_of t) ~default:loc in
      let head, args = spine_of [] t in
      (match strip head with
       | Surface.Var n when String.equal n func_name ->
         if List.length args <> arity
         then
           Reporter.fatalf
             ~loc:here
             Elab_error
             "recursive call to `%s` must be fully applied (%d args), got %d"
             func_name
             arity
             (List.length args);
         let _, target_arg = List.nth args target_pos in
         (match strip target_arg with
          | Surface.Var v when List.mem_assoc v rec_arg_to_ih ->
            let ih = List.assoc v rec_arg_to_ih in
            let trailing =
              List.filteri (fun i _ -> i > target_pos) args
              |> List.map (fun (impl, a) -> impl, rw a)
            in
            List.fold_left
              (fun acc (impl, a) -> Surface.App (impl, acc, a))
              (Surface.Var ih)
              trailing
          | _ ->
            Reporter.fatalf
              ~loc:(Option.value (loc_of target_arg) ~default:here)
              Elab_error
              "non-structural recursive call to `%s` in clause body"
              func_name)
       | _ ->
         (* Not a recursive call — recurse into f and args, preserving the
            original implicit flag on each App node. *)
         let args' = List.map (fun (impl, a) -> impl, rw a) args in
         List.fold_left (fun acc (impl, a) -> Surface.App (impl, acc, a)) (rw head) args')
    | Surface.Lambda b -> Surface.Lambda { b with bound = rw b.bound }
    | Surface.TypedLambda (b, body) ->
      Surface.TypedLambda ({ b with bound = rw b.bound }, rw body)
    | Surface.Pi (b, body) -> Surface.Pi ({ b with bound = rw b.bound }, rw body)
    | Surface.Max (a, b) -> Surface.Max (rw a, rw b)
    | Surface.Var _ | Surface.Universe | Surface.Hole | Surface.Goal _ -> t
  in
  rw body
;;

(* Build a Surface preterm body for an Elim_def. The result represents the
   inner eliminator call; callers (KTopElimDef_HaveType) wrap it with outer
   `\x1 ... \xN ->` lambdas, one per name in `intros`. `intros` lists every
   binder on the guard line (matching clause-pattern positions): the first
   `np` names correspond to the function's params, the rest to past-params
   Pi-layers of `signature`.

   `signature` is the result_ty (the part after `:`) — its Pi-layers are
   only the past-params ones. The target's binder sits at position
   `target_pos - np` in `signature`; the motive captures the remainder of
   `signature`'s Pi tower past the target as a function of the target. *)
let build_elim_body
      ~(loc : Asai.Range.t)
      ~(func_name : string)
      ~(params : Surface.pretype binder list)
      ~(signature : Surface.pretype)
      ~(intros : string list)
      ~(target : string)
      ~(clauses : Surface.clause list)
  : Surface.preterm
  =
  let np = List.length params in
  let n_intros = List.length intros in
  let target_pos =
    let rec go i = function
      | [] -> Reporter.fatalf ~loc Elab_error "elim target `%s` not among intros" target
      | x :: _ when String.equal x target -> i
      | _ :: xs -> go (i + 1) xs
    in
    go 0 intros
  in
  (* Target's Pi-binder is at position (target_pos - np) in `signature`
     (signature has only the past-params Pi-layers). Take its domain — the
     target's type — as a Surface term. *)
  let target_type_surface : Surface.pretype =
    let rec find_dom ~loc n s =
      match s with
      | Surface.Located { value; loc = inner } ->
        find_dom ~loc:(Option.value inner ~default:loc) n value
      | Surface.Pi (binder, cod) ->
        if n = 0 then binder.bound else find_dom ~loc (n - 1) cod
      | _ ->
        Reporter.fatalf
          ~loc
          Elab_error
          "elim: signature has fewer Pi-layers than required"
    in
    find_dom ~loc (target_pos - np) signature
  in
  let ind_head, data_args =
    let rec head = function
      | Surface.App (_, f, _) -> head f
      | Surface.Located { value = t; _ } -> head t
      | Surface.Var n -> n
      | _ ->
        Reporter.fatalf
          ~loc:(Option.value (loc_of target_type_surface) ~default:loc)
          Elab_error
          "elim: target's type head is not an inductive"
    in
    let h = head target_type_surface in
    let args = Surface.applied_spine target_type_surface in
    h, args
  in
  let info : ElabData.ind_info =
    match Context.S.resolve [ ind_head ] with
    | Some (_, `Inductive info) -> info
    | _ -> Reporter.fatalf ~loc Elab_error "elim: `%s` is not an inductive" ind_head
  in
  let ctors = ElabData.arities_of info in
  let ctor_infos = info.infos in
  let is_ctor name = List.exists (fun (n, _) -> String.equal n name) ctors in
  let normalize = function
    | Surface.PVar n when is_ctor n -> Surface.PCon (n, [])
    | p -> p
  in
  (* Motive: `\<target> -> peel_pi_surface (target_pos - np + 1) signature`. *)
  let motive : Surface.preterm =
    let body = peel_pi_surface ~loc (target_pos - np + 1) signature in
    Surface.Lambda { name = target; bound = body; implicit = false }
  in
  let trailing_intros = List.filteri (fun i _ -> i > target_pos) intros in
  (* Per-ctor case arm. *)
  let case_args : Surface.preterm list =
    List.map
      (fun (ctor_name, arity) ->
         let info =
           List.find
             (fun (i : ElabData.ctor_info) -> String.equal i.ctor_name ctor_name)
             ctor_infos
         in
         let clause =
           match
             List.find_opt
               (fun (c : Surface.clause) ->
                  match Option.map normalize (List.nth_opt c.patterns target_pos) with
                  | Some (Surface.PCon (cn, _)) -> String.equal cn ctor_name
                  | _ -> false)
               clauses
           with
           | Some c -> c
           | None ->
             Reporter.fatalf
               ~loc
               Elab_error
               "elim on `%s`: no clause for constructor `%s`"
               ind_head
               ctor_name
         in
         let clause_loc = Option.value (loc_of clause.body) ~default:loc in
         if not (String.equal clause.head func_name)
         then
           Reporter.fatalf
             ~loc:clause_loc
             Elab_error
             "elim clause head `%s` does not match function name `%s`"
             clause.head
             func_name;
         let vs =
           match Option.map normalize (List.nth_opt clause.patterns target_pos) with
           | Some (Surface.PCon (_, vs)) -> vs
           | _ -> []
         in
         if List.length vs <> arity
         then
           Reporter.fatalf
             ~loc:clause_loc
             Elab_error
             "constructor `%s` expects %d field-binders, got %d"
             ctor_name
             arity
             (List.length vs);
         let rec_arg_to_ih : (string * string) list =
           List.filter_map
             (fun (v, kind) ->
                match (kind : ElabData.binder_kind) with
                | ElabData.Recursive _ -> Some (v, "ih-" ^ v)
                | ElabData.Regular -> None)
             (List.combine vs info.binder_kinds)
         in
         let trailing_pattern_names =
           List.filteri (fun i _ -> i > target_pos) clause.patterns
           |> List.map (function
             | Surface.PVar n -> n
             | Surface.PCon _ ->
               Reporter.fatalf
                 ~loc:clause_loc
                 Elab_error
                 "elim: pattern at non-target position must be a variable")
         in
         if List.length trailing_pattern_names <> List.length trailing_intros
         then
           Reporter.fatalf
             ~loc:clause_loc
             Elab_error
             "elim clause `%s`: expected %d trailing pattern(s), got %d"
             ctor_name
             (List.length trailing_intros)
             (List.length trailing_pattern_names);
         let rewritten_body =
           rewrite_recursive_calls
             ~loc:clause_loc
             ~func_name
             ~arity:n_intros
             ~target_pos
             ~rec_arg_to_ih
             clause.body
         in
         let with_trailing =
           List.fold_right
             (fun n body -> Surface.Lambda { name = n; bound = body; implicit = false })
             trailing_pattern_names
             rewritten_body
         in
         List.fold_right
           (fun (v, kind) body ->
              let inner =
                match (kind : ElabData.binder_kind) with
                | ElabData.Recursive _ ->
                  Surface.Lambda { name = "ih-" ^ v; bound = body; implicit = false }
                | ElabData.Regular -> body
              in
              Surface.Lambda { name = v; bound = inner; implicit = false })
           (List.combine vs info.binder_kinds)
           with_trailing)
      ctors
  in
  let elim_call =
    List.fold_left
      (fun acc a -> Surface.App (false, acc, a))
      (Surface.Var (ind_head ^ "-elim"))
      (data_args @ [ Surface.Var target; motive ] @ case_args)
  in
  List.fold_left
    (fun acc n -> Surface.App (false, acc, Surface.Var n))
    elim_call
    trailing_intros
;;

(* Walk through the move list, peeling Pi-layers off `goal` and constructing
   a Surface preterm body that the elaborator will later check against the
   full Pi type. `position` is the next LHS pattern position to consult for
   binder naming (counted from the start of params + intros).
   `signature` and `n_params` are unchanged across recursion; they're used at
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
       let ctx' = bind ctx name a in
       let inner =
         walk_moves ~loc ctx' cod signature n_params rest clauses (position + 1)
       in
       Surface.Lambda { name; bound = inner; implicit = false }
     | other ->
       Reporter.fatalf
         ~loc
         Elab_error
         "`<= intro` needs a function type, got `%s`"
         ([%show: Core.value] other))
  | Surface.Split :: rest ->
    if rest <> []
    then
      Reporter.fatalf
        ~loc
        Elab_error
        "v1 only allows one optional `<= split` at the end of the move list";
    let target_name, target_ty =
      match ctx.names, ctx.types with
      | Bwd.Snoc (_, n), Bwd.Snoc (_, t) -> n, t
      | _ -> Reporter.fatalf ~loc Elab_error "`<= split` requires a preceding `<= intro`"
    in
    let pattern_position = position - 1 in
    let ind_head =
      match Evaluation.force_head target_ty with
      | Core.IndType (h, _) -> h
      | other ->
        Reporter.fatalf
          ~loc
          Elab_error
          "`<= split`: target type must be an inductive, got `%s`"
          ([%show: Core.value] other)
    in
    let ctors =
      match Context.S.resolve [ ind_head ] with
      | Some (_, `Inductive info) -> ElabData.arities_of info
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
         | Some (Surface.PVar _) ->
           Reporter.fatalf
             ~loc:cloc
             Elab_error
             "expected constructor pattern at split position, got variable"
         | None ->
           Reporter.fatalf ~loc:cloc Elab_error "clause `%s` has too few patterns" c.head)
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
           List.fold_right
             (fun v body -> Surface.Lambda { name = v; bound = body; implicit = false })
             vs
             clause.body)
        ctors
    in
    let motive_body = peel_pi_surface ~loc (pattern_position + 1 - n_params) signature in
    let motive : Surface.preterm =
      Surface.Lambda { name = target_name; bound = motive_body; implicit = false }
    in
    (* Extract the target's type as a Surface preterm so we can read off the
       data-type's params + deps to prepend to the eliminator's spine. The
       target's type is the domain of the (pattern_position - n_params)-th
       Pi-layer of `signature`. *)
    let target_type_surface : Surface.pretype =
      let rec find_dom ~loc n s =
        match s with
        | Surface.Located { value; loc = inner } ->
          find_dom ~loc:(Option.value inner ~default:loc) n value
        | Surface.Pi (binder, cod) ->
          if n = 0 then binder.bound else find_dom ~loc (n - 1) cod
        | _ ->
          Reporter.fatalf
            ~loc
            Elab_error
            "stack-def: cannot locate target type in signature"
      in
      find_dom ~loc (pattern_position - n_params) signature
    in
    let data_args : Surface.preterm list = Surface.applied_spine target_type_surface in
    List.fold_left
      (fun acc arg -> Surface.App (false, acc, arg))
      (Surface.Var (ind_head ^ "-elim"))
      (data_args @ [ Surface.Var target_name; motive ] @ case_args)
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
  | KPi_HaveDom of t * string * bool * Surface.pretype
  | KPi_HaveCod of t * string * bool * Core.term * Level.level
  | KLam_Body of t * string * bool
  | KTypedLam_HaveDom of t * string * bool * Surface.preterm
  | KTypedLam_HaveBody of t * string * bool * Core.term * Core.value_ty
  | KMax_HaveLeft of t * Surface.preterm
  | KMax_HaveRight of t * Level.level
  | KEnsureUniverse of t
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
  | KTopLet_HaveBody of t * string * Core.value_ty
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
      * string
      * Surface.clause list
  | KTopElimDef_HaveType of
      t
      * string
      * Surface.pretype binder list
      * Surface.pretype
      * string list
      * string
      * Surface.clause list

type machine =
  { mutable goals : goal list
  ; mutable result : produced option
  ; mutable ctx : local_ctx
  ; mutable saved_ctx : local_ctx list
  ; module_name : string
  ; goal_counter : int ref
  ; pending_goals : int ref
  }

let make_machine ~(module_name : string) ~(goal_counter : int ref) () : machine =
  { goals = []
  ; result = None
  ; ctx = empty_ctx
  ; saved_ctx = []
  ; module_name
  ; goal_counter
  ; pending_goals = ref 0
  }
;;

let save_ctx (m : machine) : unit = m.saved_ctx <- m.ctx :: m.saved_ctx

let restore_ctx (m : machine) : unit =
  match m.saved_ctx with
  | c :: rest ->
    m.ctx <- c;
    m.saved_ctx <- rest
  | [] -> Reporter.fatalf Elab_error "StackElab: restore_ctx on empty saved_ctx"
;;

let push (m : machine) (g : goal) : unit = m.goals <- g :: m.goals

let take_result (m : machine) : produced =
  match m.result with
  | Some p ->
    m.result <- None;
    p
  | None -> Reporter.fatalf Elab_error "StackElab: take_result on empty result"
;;

let resolve_goal_name (m : machine) (n : string option) : string =
  match n with
  | Some s -> s
  | None ->
    let i = !(m.goal_counter) in
    m.goal_counter := i + 1;
    string_of_int i
;;

(* Context-aware pretty-printer for Core.value used by goal reports.
   Replaces de Bruijn levels (`$N`) with the surface name from ctx.names,
   and renders levels and universes in a user-facing form. Falls back to
   `$N` when a level escapes the supplied context (e.g. closure-feed
   placeholders used while descending into VPi/VLambda). *)
let pretty_local_name (ctx : local_ctx) (lvl : int) : string =
  if lvl >= 0 && lvl < ctx.lvl
  then Bwd.nth ctx.names (ctx.lvl - 1 - lvl)
  else Printf.sprintf "$%d" lvl
;;

let rec pretty_level_atom (l : Level.level) : string =
  match l with
  | Level.LZero -> "0"
  | Level.LVar v -> v
  | Level.LSuc _ | Level.LMax _ -> "(" ^ pretty_level l ^ ")"

and pretty_level (l : Level.level) : string =
  match l with
  | Level.LZero -> "0"
  | Level.LVar v -> v
  | Level.LSuc l' -> "S " ^ pretty_level_atom l'
  | Level.LMax (a, b) -> pretty_level_atom a ^ " ⊔ " ^ pretty_level_atom b
;;

let pretty_universe (l : Level.level) : string =
  match l with
  | Level.LZero -> "𝓤"
  | _ -> "𝓤(" ^ pretty_level l ^ ")"
;;

let pretty_metavar (Core.MetaVar i : Core.metavar) : string = Printf.sprintf "?%d" i

let rec pretty_value (ctx : local_ctx) (v : Core.value) : string =
  match v with
  | Core.Universe l -> pretty_universe l
  | Core.RigidLocal (lvl, spine) -> pretty_neutral ctx (pretty_local_name ctx lvl) spine
  | Core.Var (n, spine) -> pretty_neutral ctx n spine
  | Core.IndType (n, spine) -> pretty_neutral ctx n spine
  | Core.Label (n, spine) -> pretty_neutral ctx n spine
  | Core.Flex (m, spine) -> pretty_neutral ctx (pretty_metavar m) spine
  | Core.Elim ({ elim_name; _ }, spine) -> pretty_neutral ctx elim_name spine
  | Core.VPi ({ name; bound; implicit }, closure) ->
    let body = closure (Core.RigidLocal (ctx.lvl, Bwd.Emp)) in
    let ctx' = bind ctx name bound in
    let l, r = if implicit then "{", "}" else "(", ")" in
    Printf.sprintf
      "%s%s : %s%s -> %s"
      l
      name
      (pretty_value ctx bound)
      r
      (pretty_value ctx' body)
  | Core.VLambda { name; bound = closure; implicit } ->
    let body = closure (Core.RigidLocal (ctx.lvl, Bwd.Emp)) in
    (* Binder type is not stored on VLambda; placeholder type doesn't affect
       the printed body. *)
    let ctx' = bind ctx name (Core.Universe Level.LZero) in
    if implicit
    then Printf.sprintf "(fun {%s} => %s)" name (pretty_value ctx' body)
    else Printf.sprintf "(fun %s => %s)" name (pretty_value ctx' body)
  | Core.VLift { from_lvl; to_lvl; ty } ->
    Printf.sprintf
      "lift[%s→%s] %s"
      (pretty_level from_lvl)
      (pretty_level to_lvl)
      (pretty_value ctx ty)
  | Core.VLiftTerm { from_lvl; to_lvl; ty; tm } ->
    Printf.sprintf
      "liftₜ[%s→%s] (%s : %s)"
      (pretty_level from_lvl)
      (pretty_level to_lvl)
      (pretty_value ctx tm)
      (pretty_value ctx ty)
  | Core.VUnliftTerm { from_lvl; to_lvl; ty; tm } ->
    Printf.sprintf
      "unliftₜ[%s→%s] (%s : %s)"
      (pretty_level from_lvl)
      (pretty_level to_lvl)
      (pretty_value ctx tm)
      (pretty_value ctx ty)

and pretty_neutral (ctx : local_ctx) (head : string) (spine : Core.value bwd) : string =
  if Bwd.is_empty spine
  then head
  else (
    let args = List.map (pretty_arg ctx) (Bwd.to_list spine) in
    head ^ " " ^ String.concat " " args)

and pretty_arg (ctx : local_ctx) (v : Core.value) : string =
  match v with
  | Core.Universe _
  | Core.RigidLocal (_, Emp)
  | Core.Var (_, Emp)
  | Core.IndType (_, Emp)
  | Core.Label (_, Emp)
  | Core.Flex (_, Emp) -> pretty_value ctx v
  | _ -> "(" ^ pretty_value ctx v ^ ")"
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
  let names = Bwd.to_list m.ctx.names in
  let types = Bwd.to_list m.ctx.types in
  List.iter2
    (fun n ty ->
       Buffer.add_string buf (Printf.sprintf "  %s : %s\n" n (pretty_value m.ctx ty)))
    names
    types;
  Buffer.add_string buf "  --- target ---\n";
  Buffer.add_string buf (Printf.sprintf "  %s" (pretty_value m.ctx target));
  Reporter.emitf ~loc Goal_report "%s" (Buffer.contents buf)
;;

let name_of_top : Surface.top -> string = function
  | Surface.Let (n, _, _, _) -> n
  | Surface.Data { name; _ } -> name
  | Surface.Stack_def { name; _ } -> name
  | Surface.Elim_def { name; _ } -> name
  | Surface.Universe_decl _ -> "<universe_decl>"
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
  | GInfer (_, Var x) ->
    (match resolve_local m.ctx x with
     | Some i -> m.result <- Some (PTermType (Core.LocalVar i, local_type m.ctx i))
     | None ->
       (match resolve_universe_var x with
        | Some l ->
          m.result <- Some (PTermType (Core.Universe l, Core.Universe (Level.lsuc l)))
        | None -> m.result <- Some (PTermType (Core.Var x, Context.lookup x))))
  | GInferType (loc, Goal name_opt) ->
    let name = resolve_goal_name m name_opt in
    emit_goal_report ~loc m ~name ~target:(Core.Universe Level.LZero);
    incr m.pending_goals;
    m.result <- Some (PType (Meta.meta_fresh m.ctx.lvl, Level.LZero))
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
            ([%show: Core.term] tm)
            ([%show: Core.value] other))
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
         ([%show: Core.value] ty))
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
          else Reporter.fatalf ~loc Elab_error "Bad apply at %s" ([%show: Core.term] f_tm)
        | ty ->
          Reporter.fatalf
            ~loc
            Type_error
            "cannot apply to `(%s) : %s`"
            ([%show: Core.term] f_tm)
            ([%show: Core.value_ty] ty))
     | other ->
       Reporter.fatalf Elab_error "KApp_HaveFn: bad result %s" ([%show: produced] other))
  | KApp_HaveArg (_loc, f_tm, b) ->
    (match take_result m with
     | PTerm arg_tm ->
       let arg_val = Evaluation.eval m.ctx.env arg_tm in
       m.result <- Some (PTermType (Core.App (f_tm, arg_tm), b arg_val))
     | other ->
       Reporter.fatalf Elab_error "KApp_HaveArg: bad result %s" ([%show: produced] other))
  | GInfer (loc, Lambda _) -> Reporter.fatalf ~loc Elab_error "cannot infer lambda term"
  | GCheck (_loc, Hole, _) -> m.result <- Some (PTerm (Meta.meta_fresh m.ctx.lvl))
  | GInfer (_loc, Hole) ->
    let ty = Evaluation.eval m.ctx.env (Meta.meta_fresh m.ctx.lvl) in
    let tm = Meta.meta_fresh m.ctx.lvl in
    m.result <- Some (PTermType (tm, ty))
  | GCheck (loc, Goal name_opt, ty) ->
    let name = resolve_goal_name m name_opt in
    emit_goal_report ~loc m ~name ~target:ty;
    incr m.pending_goals;
    m.result <- Some (PTerm (Meta.meta_fresh m.ctx.lvl))
  | GInfer (loc, Goal name_opt) ->
    let name = resolve_goal_name m name_opt in
    let ty_tm = Meta.meta_fresh m.ctx.lvl in
    let ty_val = Evaluation.eval m.ctx.env ty_tm in
    emit_goal_report ~loc m ~name ~target:ty_val;
    incr m.pending_goals;
    m.result <- Some (PTermType (Meta.meta_fresh m.ctx.lvl, ty_val))
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
         ([%show: Core.term] other_tm)
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
         ([%show: Core.term] other_tm)
     | other ->
       Reporter.fatalf
         Elab_error
         "KMax_HaveRight: bad result %s"
         ([%show: produced] other))
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
          Unification.unify ~loc m.ctx.lvl expected infer_ty;
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
       push m (KTopLet_HaveBody (loc, name, typ_val));
       push m (GCheck (loc, term, typ_val))
     | other ->
       Reporter.fatalf
         Elab_error
         "KTopLet_HaveType: bad result %s"
         ([%show: produced] other))
  | KTopLet_HaveBody (_loc, name, typ_val) ->
    (match take_result m with
     | PTerm term ->
       Context.S.include_singleton
         ~context_visible:`Visible
         ~context_export:`Export
         ([ name ], (typ_val, `Constructor));
       let body_val = Evaluation.eval m.ctx.env term in
       Env.S.include_singleton
         ~context_visible:`Visible
         ~context_export:`Export
         ([ name ], (body_val, `Constructor));
       Env.register_definition name body_val;
       m.result <- Some PUnit
     | other ->
       Reporter.fatalf
         Elab_error
         "KTopLet_HaveBody: bad result %s"
         ([%show: produced] other))
  | GTopStackDef (loc, name, bindings, result_ty, moves, clauses) ->
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
       push m (KTopLet_HaveBody (loc, name, typ_val));
       push m (GCheck (loc, term, typ_val))
     | other ->
       Reporter.fatalf
         Elab_error
         "KTopStackDef_HaveType: bad result %s"
         ([%show: produced] other))
  | GTopElimDef (loc, name, bindings, result_ty, intros, target, clauses) ->
    let typ : Surface.pretype =
      List.fold_right
        (fun binding return_ty -> Surface.Pi (binding, return_ty))
        bindings
        result_ty
    in
    push
      m
      (KTopElimDef_HaveType (loc, name, bindings, result_ty, intros, target, clauses));
    push m (GInferType (loc, typ))
  | KTopElimDef_HaveType (loc, name, bindings, signature, intros, target, clauses) ->
    (match take_result m with
     | PType (typ_tm, _) ->
       let typ_val = Evaluation.eval m.ctx.env typ_tm in
       let elim_inner =
         build_elim_body
           ~loc
           ~func_name:name
           ~params:bindings
           ~signature
           ~intros
           ~target
           ~clauses
       in
       (* `intros` lists every binder on the guard line — one per Pi-layer
          of the full function type (params + past-params). Wrap with intros
          lambdas only; the outer Pi-layers from `bindings` are covered by
          intros[0..np-1]. *)
       let term : Surface.preterm =
         List.fold_right
           (fun n body -> Surface.Lambda { name = n; bound = body; implicit = false })
           intros
           elim_inner
       in
       push m (KTopLet_HaveBody (loc, name, typ_val));
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
             ([%show: Core.value] other)
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
           ([%show: Level.level] user_sort)
           ([%show: Level.level] inferred_sort);
       let infos = List.map (ElabData.analyze_ctor ~ind_name:name ~params) ctors in
       let ind_info : ElabData.ind_info = { params; deps; ind_ty; ctors; infos } in
       Context.S.include_singleton
         ~context_visible:`Visible
         ~context_export:`Export
         ([ name ], (typ_val, `Inductive ind_info));
       Env.S.include_singleton
         ~context_visible:`Visible
         ~context_export:`Export
         ([ name ], (Core.IndType (name, Bwd.Emp), `Constructor));
       List.iter (bind_constructor ~loc m.ctx params) ctors;
       let elim_typ : Surface.pretype =
         ElabData.eliminator_type ~name ~params ~deps ~ind_ty ctors
       in
       let elim_name = name ^ "-elim" in
       let elim_typ_tm = check_type ~loc m.ctx elim_typ in
       let elim_typ_val = Evaluation.eval m.ctx.env elim_typ_tm in
       Context.S.include_singleton
         ~context_visible:`Visible
         ~context_export:`Export
         ([ elim_name ], (elim_typ_val, `Constructor));
       let reducer =
         ElabData.build_elim_reducer ~ind_name:name ~elim_name ~params ~deps ctors
       in
       let elim_value = Core.Elim ({ elim_name; reducer }, Bwd.Emp) in
       Env.S.include_singleton
         ~context_visible:`Visible
         ~context_export:`Export
         ([ elim_name ], (elim_value, `Constructor));
       m.result <- Some PUnit
     | other ->
       Reporter.fatalf
         Elab_error
         "KTopData_HaveType: bad result %s"
         ([%show: produced] other))
  | GTopData (_, _) -> Reporter.fatalf Elab_error "GTopData: payload is not Data"

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
  let m = make_machine ~module_name:"_internal" ~goal_counter:(ref 0) () in
  m.ctx <- ctx;
  push m (GInferType (loc, pretype));
  match drive m with
  | PType (tm, l) -> tm, l
  | other -> Reporter.fatalf ~loc Elab_error "infer_type: %s" ([%show: produced] other)

and check_type ~loc (ctx : local_ctx) (pretype : Surface.pretype) : Core.term =
  fst (infer_type ~loc ctx pretype)

and bind_constructor
      ~loc
      (ctx : local_ctx)
      (params : Surface.pretype binder list)
      ({ name; bound = typ; _ } : Surface.pretype binder)
  : unit
  =
  let typ = close_ctor_type params typ in
  let ctor_ty_tm = check_type ~loc ctx typ in
  let ctor_ty = Evaluation.eval ctx.env ctor_ty_tm in
  Context.S.include_singleton ([ name ], (ctor_ty, `Constructor));
  Env.S.include_singleton ([ name ], (Core.Label (name, Bwd.Emp), `Constructor))
;;

(* Internal: run a thunk under all elaboration effect handlers. *)
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

(* Test harness: run a single GInfer to completion against the empty ctx. *)
let infer_for_test (p : Surface.preterm) : Core.term * Core.value =
  with_handlers
  @@ fun () ->
  let m = make_machine ~module_name:"test" ~goal_counter:(ref 0) () in
  push m (GInfer (Asai.Range.of_lex_range (Lexing.dummy_pos, Lexing.dummy_pos), p));
  match drive m with
  | PTermType (tm, ty) -> tm, ty
  | other -> Reporter.fatalf Elab_error "infer_for_test: got %s" ([%show: produced] other)
;;

let%expect_test "infer Universe" =
  let tm, ty = infer_for_test Surface.Universe in
  Printf.printf "%s : %s" ([%show: Core.term] tm) ([%show: Core.value] ty);
  [%expect {| 𝓤 : 𝓤((Level.LSuc Level.LZero)) |}]
;;

let%expect_test "infer Var bound locally" =
  with_handlers (fun () ->
    let m = make_machine ~module_name:"test" ~goal_counter:(ref 0) () in
    m.ctx <- bind m.ctx "x" (Core.Universe Level.LZero);
    push
      m
      (GInfer
         (Asai.Range.of_lex_range (Lexing.dummy_pos, Lexing.dummy_pos), Surface.Var "x"));
    let tm, ty =
      match drive m with
      | PTermType (a, b) -> a, b
      | _ -> failwith "wrong shape"
    in
    Printf.printf "%s : %s" ([%show: Core.term] tm) ([%show: Core.value] ty));
  [%expect {| $0 : 𝓤 |}]
;;

let%expect_test "infer Pi" =
  let p =
    Surface.Pi
      ({ name = "x"; bound = Surface.Universe; implicit = false }, Surface.Universe)
  in
  let tm, ty = infer_for_test p in
  Printf.printf "%s : %s" ([%show: Core.term] tm) ([%show: Core.value] ty);
  [%expect
    {| ∀ (x : 𝓤) -> 𝓤 : 𝓤((Level.LMax ((Level.LSuc Level.LZero), (Level.LSuc Level.LZero)))) |}]
;;

let%expect_test "check Lambda against Pi" =
  let p = Surface.Lambda { name = "x"; bound = Surface.Var "x"; implicit = false } in
  let expected_ty =
    Core.VPi
      ( { name = "x"; bound = Core.Universe Level.LZero; implicit = false }
      , fun _ -> Core.Universe Level.LZero )
  in
  with_handlers (fun () ->
    let m = make_machine ~module_name:"test" ~goal_counter:(ref 0) () in
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
    let m = make_machine ~module_name:"test" ~goal_counter:(ref 0) () in
    let loc = Asai.Range.of_lex_range (Lexing.dummy_pos, Lexing.dummy_pos) in
    (* Bind x : U at level 0 *)
    m.ctx <- bind m.ctx "x" (Core.Universe Level.LZero);
    (* Bind f : (U -> U) at level 1 *)
    let f_ty =
      Core.VPi
        ( { name = "a"; bound = Core.Universe Level.LZero; implicit = false }
        , fun _ -> Core.Universe Level.LZero )
    in
    m.ctx <- bind m.ctx "f" f_ty;
    push m (GInfer (loc, Surface.App (false, Surface.Var "f", Surface.Var "x")));
    match drive m with
    | PTermType (tm, ty) ->
      Printf.printf "tm: %s\nty: %s" ([%show: Core.term] tm) ([%show: Core.value] ty)
    | _ -> failwith "wrong shape");
  [%expect
    {|
    tm: $0 $1
    ty: 𝓤
  |}]
;;

let%expect_test "rewrite_recursive_calls: case-suc of add" =
  (* Body: `add' m n` with `m` being a recursive case-arg. *)
  let body =
    Surface.App
      (false, Surface.App (false, Surface.Var "add'", Surface.Var "m"), Surface.Var "n")
  in
  let rewritten =
    rewrite_recursive_calls
      ~loc:(Asai.Range.of_lex_range (Lexing.dummy_pos, Lexing.dummy_pos))
      ~func_name:"add'"
      ~arity:2
      ~target_pos:0
      ~rec_arg_to_ih:[ "m", "ih-m" ]
      body
  in
  print_string @@ [%show: Surface.preterm] rewritten;
  [%expect {| (ih-m n) |}]
;;

let%expect_test "rewrite_recursive_calls: non-recursive call left alone" =
  let body =
    Surface.App
      (false, Surface.App (false, Surface.Var "foo", Surface.Var "m"), Surface.Var "n")
  in
  let rewritten =
    rewrite_recursive_calls
      ~loc:(Asai.Range.of_lex_range (Lexing.dummy_pos, Lexing.dummy_pos))
      ~func_name:"add'"
      ~arity:2
      ~target_pos:0
      ~rec_arg_to_ih:[ "m", "ih-m" ]
      body
  in
  print_string @@ [%show: Surface.preterm] rewritten;
  [%expect {| ((foo m) n) |}]
;;

let%expect_test "report named goal in check mode" =
  with_handlers_emitting (fun () ->
    let m = make_machine ~module_name:"nat" ~goal_counter:(ref 0) () in
    m.ctx <- bind m.ctx "A" (Core.Universe Level.LZero);
    m.ctx <- bind m.ctx "x" (Core.RigidLocal (0, Bwd.Emp));
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
    [Reporter.Message.Goal_report] ?nat/here
      --- context ---
      A : 𝓤
      x : A
      --- target ---
      A
    pending=1
    |}]
;;

let%expect_test "auto-numbered goals" =
  with_handlers_emitting (fun () ->
    let counter = ref 0 in
    let m = make_machine ~module_name:"nat" ~goal_counter:counter () in
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
    [Reporter.Message.Goal_report] ?nat/0
      --- context ---
      --- target ---
      𝓤
    [Reporter.Message.Goal_report] ?nat/1
      --- context ---
      --- target ---
      𝓤
    pending=2 counter=2
    |}]
;;

let check_top
      ~(module_name : string)
      ~(goal_counter : int ref)
      ~(loc : Asai.Range.t)
      (top : Surface.top)
  : unit
  =
  let m = make_machine ~module_name ~goal_counter () in
  let g =
    match top with
    | Surface.Universe_decl names -> GTopUniverseDecl names
    | Surface.Let (name, bindings, result_ty, body) ->
      GTopLet (loc, name, bindings, result_ty, body)
    | Surface.Data _ as d -> GTopData (loc, d)
    | Surface.Stack_def { name; params; signature; moves; clauses } ->
      GTopStackDef (loc, name, params, signature, moves, clauses)
    | Surface.Elim_def { name; params; signature; intros; target; clauses } ->
      GTopElimDef (loc, name, params, signature, intros, target, clauses)
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

let check_module (file : Surface.t) : unit =
  let module_name = Filename.chop_extension @@ Filename.basename file.name in
  Eio.traceln "checking [module] %s (%s)" module_name file.name;
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
  Context.S.section [ module_name ]
  @@ fun () ->
  Env.S.section [ module_name ]
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
       check_top ~module_name ~goal_counter ~loc top.value)
    file.tops
;;
