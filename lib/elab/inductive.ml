module Syntax = Violet_kernel.Syntax
module Context_view = Violet_kernel.Context_view
module Pretty = Violet_kernel.Pretty
module Evaluation = Wiring.Eval
open Syntax
open Asai.Range
open Surface_utils
open Bwd

let loc_or (default : Asai.Range.t) (t : Surface.preterm) : Asai.Range.t =
  Option.value (loc_of t) ~default
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

let drop_key (name : string) (assoc : (string * 'a) list) : (string * 'a) list =
  List.filter (fun (k, _) -> not (String.equal k name)) assoc
;;

(* A stateful name-freshener: pick names that avoid collisions with an
   evolving "known" set. [freshen base] returns the first variant of
   [base] (adding `'`s as needed) that isn't already known, and records
   the chosen name. [claim name] records [name] without freshening, for
   user-written binders that we want to leave alone but still want
   subsequent freshenings to skip. *)
type freshener =
  { freshen : string -> string
  ; claim : string -> unit
  }

let make_freshener (initial : string list) : freshener =
  let known = ref initial in
  let freshen (base : string) : string =
    let rec go cand =
      if List.mem cand !known
      then go (cand ^ "'")
      else (
        known := cand :: !known;
        cand)
    in
    go base
  in
  let claim (name : string) : unit = known := name :: !known in
  { freshen; claim }
;;

(* Rename free Var occurrences in a Surface preterm. Respects binders: when
   we descend under a Lambda/TypedLambda/Pi whose name shadows a key in the
   renaming, that key is dropped for the inner scope. *)
let rename_vars_surface (renaming : (string * string) list) (t : Surface.preterm)
  : Surface.preterm
  =
  match renaming with
  | [] -> t
  | _ ->
    map_free_vars
      ~on_var:(fun ren n ->
        match List.assoc_opt n ren with
        | Some n' -> Surface.Var [ n' ]
        | None -> Surface.Var [ n ])
      ~enter:drop_key
      renaming
      t
;;

(* Promote bare references to constructors of `ind_head` to their qualified
   form `Var [ind_head; n]`. Used to auto-open the scrutinee's namespace
   inside `elim` clause bodies, so users can write `suc (add m n)` instead
   of `Nat/suc (add m n)`. Lambda/TypedLambda/Pi binders shadow promotions
   within their scope; the initial `shadowed` set names the binders that
   already wrap the body from above (intros, params, ctor field-binders,
   IH names, trailing pattern names). *)
let qualify_ctor_names
      ~(ind_head : string)
      ~(ctor_names : string list)
      ~(shadowed : string list)
      (body : Surface.preterm)
  : Surface.preterm
  =
  let is_ctor n = List.mem n ctor_names in
  map_free_vars
    ~on_var:(fun shadowed n ->
      if is_ctor n && not (List.mem n shadowed)
      then Surface.Var [ ind_head; n ]
      else Surface.Var [ n ])
    ~enter:(fun name shadowed -> name :: shadowed)
    shadowed
    body
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
      let here = loc_or loc t in
      let head, args = spine_of [] t in
      (match strip head with
       | Surface.Var [ n ] when String.equal n func_name ->
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
          | Surface.Var [ v ] when List.mem_assoc v rec_arg_to_ih ->
            let ih = List.assoc v rec_arg_to_ih in
            let trailing =
              List.filteri (fun i _ -> i > target_pos) args
              |> List.map (fun (impl, a) -> impl, rw a)
            in
            List.fold_left
              (fun acc (impl, a) -> Surface.App (impl, acc, a))
              (Surface.Var [ ih ])
              trailing
          | _ ->
            Reporter.fatalf
              ~loc:(loc_or here target_arg)
              Elab_error
              "non-structural recursive call to `%s` in clause body"
              func_name)
       | _ ->
         let args' = List.map (fun (impl, a) -> impl, rw a) args in
         List.fold_left (fun acc (impl, a) -> Surface.App (impl, acc, a)) (rw head) args')
    | Surface.Lambda b -> Surface.Lambda { b with bound = rw b.bound }
    | Surface.TypedLambda (b, body) ->
      Surface.TypedLambda ({ b with bound = rw b.bound }, rw body)
    | Surface.Pi (b, body) -> Surface.Pi ({ b with bound = rw b.bound }, rw body)
    | Surface.Max (a, b) -> Surface.Max (rw a, rw b)
    | Surface.Var _ | Surface.Universe | Surface.Hole | Surface.Goal _ -> t
    | Surface.IdAbsurd _ -> t
    | Surface.Op_soup _ ->
      Reporter.fatalf
        Elab_error
        "internal: Op_soup reached clause-body rewrite (resolver should have lowered it)"
    | Surface.RecordLit entries ->
      Surface.RecordLit (List.map (fun (f, e) -> f, rw e) entries)
    | Surface.RecordUpdate (base, entries) ->
      Surface.RecordUpdate (rw base, List.map (fun (f, e) -> f, rw e) entries)
    | Surface.Proj (e, f) -> Surface.Proj (rw e, f)
    | Surface.Inline_elim _ as t -> t
  in
  rw body
;;

(* Walk the function's full Pi tower (params ++ outer Pi-layers of
   signature) in parallel with the user's intros to produce one entry
   per Pi-binder: `(name, implicit)`. Implicit Pi-binders the user
   didn't bracket are auto-filled from the binder's own name; explicit
   Pi-binders must be matched by a bare intro. *)
let compute_effective_intros
      ~(loc : Asai.Range.t)
      ~(bindings : Surface.pretype binder list)
      ~(signature : Surface.pretype)
      ~(intros : (string * bool) list)
  : (string * bool) list
  =
  let rec walk_pi params sig_binders user =
    match params, user with
    | (_, true) :: prest, (uname, true) :: urest ->
      (uname, true) :: walk_pi prest sig_binders urest
    | (pname, true) :: prest, _ -> (pname, true) :: walk_pi prest sig_binders user
    | (_, false) :: prest, (uname, false) :: urest ->
      (uname, false) :: walk_pi prest sig_binders urest
    | (pname, false) :: _, (uname, true) :: _ ->
      Reporter.fatalf
        ~loc
        Elab_error
        "intro `{%s}` provided at explicit param `%s`"
        uname
        pname
    | (pname, false) :: _, [] ->
      Reporter.fatalf ~loc Elab_error "missing intro for explicit param `%s`" pname
    | [], _ -> walk_sig sig_binders user
  and walk_sig (bs : Surface.pretype binder list) user =
    match bs, user with
    | _, [] -> []
    | [], (uname, _) :: _ ->
      Reporter.fatalf ~loc Elab_error "intro `%s` has no matching Pi-layer" uname
    | b :: rest, ((uname, u_impl) :: urest as user) ->
      (match b.implicit, u_impl with
       | true, true -> (uname, true) :: walk_sig rest urest
       | true, false -> (Name.to_string b.name, true) :: walk_sig rest user
       | false, false -> (uname, false) :: walk_sig rest urest
       | false, true ->
         Reporter.fatalf
           ~loc
           Elab_error
           "intro `{%s}` at explicit Pi-binder `%s`"
           uname
           (Name.to_string b.name))
  in
  let param_binders =
    List.map
      (fun (b : Surface.pretype binder) -> Name.to_string b.name, b.implicit)
      bindings
  in
  walk_pi param_binders (pi_domain signature) intros
;;

(* Walk effective intros in parallel with one clause's patterns.
   Implicit slots may consume a PImpVar (rebind the slot locally) or
   be skipped (use the function-level slot name). Explicit slots
   require a bare PVar/PCon. Output length equals len(effective). *)
let align_clause_patterns
      ~(loc : Asai.Range.t)
      (effective : (string * bool) list)
      (patterns : Surface.pattern list)
  : Surface.pattern list
  =
  let rec go slots pats =
    match slots, pats with
    | [], [] -> []
    | [], _ :: _ -> Reporter.fatalf ~loc Elab_error "clause: too many patterns"
    | (_, true) :: rest_slots, Surface.PImpVar n :: rest_pats ->
      Surface.PVar n :: go rest_slots rest_pats
    | (slot_name, true) :: rest_slots, _ -> Surface.PVar slot_name :: go rest_slots pats
    | (_, false) :: rest_slots, (Surface.PVar _ as p) :: rest_pats ->
      p :: go rest_slots rest_pats
    | (_, false) :: rest_slots, (Surface.PWildcard as p) :: rest_pats ->
      p :: go rest_slots rest_pats
    | (_, false) :: rest_slots, (Surface.PCon _ as p) :: rest_pats ->
      p :: go rest_slots rest_pats
    | (_, false) :: _, Surface.PImpVar n :: _ ->
      Reporter.fatalf ~loc Elab_error "clause: `{%s}` pattern at explicit slot" n
    | (slot_name, false) :: _, [] ->
      Reporter.fatalf
        ~loc
        Elab_error
        "clause: missing pattern for explicit slot `%s`"
        slot_name
    | (_, false) :: rest_slots, (Surface.PRecord _ as p) :: rest_pats ->
      p :: go rest_slots rest_pats
  in
  go effective patterns
;;

(* Substitute free Var occurrences in a Surface preterm by full preterms.
   Like [rename_vars_surface] but maps a name to any preterm (rather than
   another name). Respects binders that shadow keys in the substitution. *)
let subst_vars_surface (subst : (string * Surface.preterm) list) (t : Surface.preterm)
  : Surface.preterm
  =
  match subst with
  | [] -> t
  | _ ->
    map_free_vars
      ~on_var:(fun s n ->
        match List.assoc_opt n s with
        | Some t' -> t'
        | None -> Surface.Var [ n ])
      ~enter:drop_key
      subst
      t
;;

(* Peel n VPi binders from a value, substituting fresh rigid_locals at the
   given start_lvl. Returns the values used (in order) and the final value
   after peeling. Forces the head before pattern-matching. *)
let rec peel_vpi (v : Core.value) (n : int) (start_lvl : int)
  : Core.value list * Core.value
  =
  if n = 0
  then [], v
  else (
    match Evaluation.force_head v with
    | Core.VPi (_, k) ->
      let local = Core.rigid_local start_lvl in
      let vs, rest = peel_vpi (k local) (n - 1) (start_lvl + 1) in
      local :: vs, rest
    | _ ->
      Reporter.fatalf
        Elab_error
        "elim: VPi peel ran out of binders (expected %d more), got `%s`"
        n
        (Pretty.pp_term Context_view.empty (Evaluation.quote 0 v)))
;;

(* Promote bare [PVar n] to [PCon (n, [])] when [n] is itself a constructor.
   The parser can't tell a nullary ctor pattern from a variable pattern, so
   both [build_elim_body] paths normalize before matching. *)
let make_normalize (ctors : (string * int) list) : Surface.pattern -> Surface.pattern =
  let is_ctor n = List.exists (fun (cn, _) -> String.equal cn n) ctors in
  function
  | Surface.PVar n when is_ctor n -> Surface.PCon (n, [])
  | p -> p
;;

(* Result of matching a single elim clause against a constructor: the names
   bound by the clause and the body after recursive-call rewriting. Used by
   both [build_elim_body] paths. *)
type processed_clause =
  { clause_loc : Asai.Range.t
  ; vs : string list (* ctor field-binder names taken from the clause's pattern *)
  ; rec_arg_to_ih : (string * string) list
  ; trailing_pattern_names : string list
  ; rewritten_body : Surface.preterm
  }

let find_matched_clauses_for_ctor
      ~(loc : Asai.Range.t)
      ~(intros : (string * bool) list)
      ~(target_pos : int)
      ~(normalize_pattern : Surface.pattern -> Surface.pattern)
      ~(ctor_name : string)
      (clauses : Surface.clause list)
  : Surface.clause list
  =
  List.filter
    (fun (c : Surface.clause) ->
       let aligned = align_clause_patterns ~loc:(loc_or loc c.body) intros c.patterns in
       match Option.map normalize_pattern (List.nth_opt aligned target_pos) with
       | Some (Surface.PCon (cn, _)) -> String.equal cn ctor_name
       | _ -> false)
    clauses
;;

let pick_head_and_deeper
      ~(loc : Asai.Range.t)
      ~(intros : (string * bool) list)
      ~(target_pos : int)
      ~(normalize_pattern : Surface.pattern -> Surface.pattern)
      (matched : Surface.clause list)
  : (Surface.clause * Surface.clause list) option
  =
  let is_pvar = function
    | Surface.PVar _ | Surface.PImpVar _ | Surface.PWildcard -> true
    | Surface.PCon _ | Surface.PRecord _ -> false
  in
  let is_head (c : Surface.clause) =
    let aligned = align_clause_patterns ~loc:(loc_or loc c.body) intros c.patterns in
    let target_sub_all_pvar =
      match Option.map normalize_pattern (List.nth_opt aligned target_pos) with
      | Some (Surface.PCon (_, sps)) -> List.for_all is_pvar sps
      | _ -> false
    in
    let non_target_all_pvar =
      List.for_all
        (fun (i, p) -> i = target_pos || is_pvar p)
        (List.mapi (fun i p -> i, p) aligned)
    in
    target_sub_all_pvar && non_target_all_pvar
  in
  let rec partition acc = function
    | [] -> List.rev acc, None
    | c :: rest when is_head c -> List.rev_append acc rest, Some c
    | c :: rest -> partition (c :: acc) rest
  in
  match partition [] matched with
  | _, None -> None
  | rest_in_order, Some head -> Some (head, rest_in_order)
;;

let expand_pcon_sub_patterns
      ~(loc : Asai.Range.t)
      ~(ctor_name : string)
      ~(implicits : bool list)
      ~(binder_names : string list)
      (user_pats : Surface.pattern list)
  : Surface.pattern list
  =
  let arity = List.length implicits in
  let explicit_arity = List.length (List.filter (fun b -> not b) implicits) in
  if List.length user_pats = arity
  then user_pats
  else if List.length user_pats = explicit_arity
  then (
    let rec go names imps user =
      match names, imps, user with
      | [], [], [] -> []
      | n :: rest_n, true :: rest_i, _ -> Surface.PVar n :: go rest_n rest_i user
      | _ :: rest_n, false :: rest_i, p :: rest_p -> p :: go rest_n rest_i rest_p
      | _ -> assert false
    in
    go binder_names implicits user_pats)
  else
    Reporter.fatalf
      ~loc
      Elab_error
      "constructor `%s` expects %d field-binders (or %d if implicits are omitted), got %d"
      ctor_name
      arity
      explicit_arity
      (List.length user_pats)
;;

let update_view_after_ctor_match
      ~(view : Surface.pattern list)
      ~(target_pos : int)
      ~(expanded : Surface.pattern list)
  : Surface.pattern list
  =
  let before = List.filteri (fun i _ -> i < target_pos) view in
  let after = List.filteri (fun i _ -> i > target_pos) view in
  before @ expanded @ after
;;

let make_siblings_with_views
      ~(loc : Asai.Range.t)
      ~(intros : (string * bool) list)
      ~(target_pos : int)
      ~(normalize_pattern : Surface.pattern -> Surface.pattern)
      ~(ctor_name : string)
      ~(implicits : bool list)
      ~(binder_names : string list)
      (matched : Surface.clause list)
  : (Surface.clause * Surface.pattern list) list
  =
  List.map
    (fun (c : Surface.clause) ->
       let aligned = align_clause_patterns ~loc:(loc_or loc c.body) intros c.patterns in
       let sub_pats =
         match Option.map normalize_pattern (List.nth_opt aligned target_pos) with
         | Some (Surface.PCon (_, sps)) -> sps
         | _ -> []
       in
       let expanded =
         expand_pcon_sub_patterns
           ~loc:(loc_or loc c.body)
           ~ctor_name
           ~implicits
           ~binder_names
           sub_pats
       in
       let view = update_view_after_ctor_match ~view:aligned ~target_pos ~expanded in
       c, view)
    matched
;;

let annotate_inline_elim_siblings
      (body : Surface.preterm)
      (siblings : (Surface.clause * Surface.pattern list) list)
  : Surface.preterm
  =
  match body with
  | Surface.Inline_elim d -> Surface.Inline_elim { d with siblings }
  | other -> other
;;

(* Accept either the full-arity form or just the explicit slots; if the
   latter, fill implicit slots with the ctor's original binder names. *)
let expand_pattern_binders
      ~(loc : Asai.Range.t)
      ~(ctor_name : string)
      ~(implicits : bool list)
      ~(binder_names : string list)
      (vs : string list)
  : string list
  =
  let arity = List.length implicits in
  let explicit_arity = List.length (List.filter (fun b -> not b) implicits) in
  if List.length vs = arity
  then vs
  else if List.length vs = explicit_arity
  then (
    let rec go names imps user =
      match names, imps, user with
      | [], [], [] -> []
      | n :: rest_n, true :: rest_i, _ -> n :: go rest_n rest_i user
      | _ :: rest_n, false :: rest_i, v :: rest_v -> v :: go rest_n rest_i rest_v
      | _ -> assert false
    in
    go binder_names implicits vs)
  else
    Reporter.fatalf
      ~loc
      Elab_error
      "constructor `%s` expects %d field-binders (or %d if implicits are omitted), got %d"
      ctor_name
      arity
      explicit_arity
      (List.length vs)
;;

let process_clause
      ~(loc : Asai.Range.t)
      ~(func_name : string)
      ~(ctor_name : string)
      ~(arity : int)
      ~(implicits : bool list)
      ~(ctor_info_ : Context.ctor_info)
      ~(intros : (string * bool) list)
      ~(target_pos : int)
      ~(n_intros : int)
      ~(n_trailing : int)
      ~(normalize_pattern : Surface.pattern -> Surface.pattern)
      (clause : Surface.clause)
  : processed_clause
  =
  let _ = arity in
  let clause_loc = loc_or loc clause.body in
  let aligned_patterns = align_clause_patterns ~loc:clause_loc intros clause.patterns in
  if not (String.equal clause.head func_name)
  then
    Reporter.fatalf
      ~loc:clause_loc
      Elab_error
      "elim clause head `%s` does not match function name `%s`"
      clause.head
      func_name;
  let raw_vs =
    match Option.map normalize_pattern (List.nth_opt aligned_patterns target_pos) with
    | Some (Surface.PCon (_, vs)) -> vs
    | _ -> []
  in
  let vs =
    List.map
      (function
        | Surface.PVar n -> n
        | Surface.PWildcard -> "_"
        | Surface.PCon _ ->
          Reporter.fatalf
            ~loc:clause_loc
            Elab_error
            "elim: deep constructor patterns at the elim target are not yet supported — \
             use a nested `<= \\elim` instead"
        | Surface.PImpVar n -> n
        | Surface.PRecord _ ->
          Reporter.fatalf
            ~loc:clause_loc
            Elab_error
            "elim: record patterns nested inside a constructor are not supported")
      raw_vs
  in
  let vs =
    expand_pattern_binders
      ~loc:clause_loc
      ~ctor_name
      ~implicits
      ~binder_names:ctor_info_.binder_names
      vs
  in
  let rec_arg_to_ih : (string * string) list =
    List.filter_map
      (fun (v, kind) ->
         match (kind : Context.binder_kind) with
         | Context.Recursive _ -> Some (v, func_name ^ " " ^ v)
         | Context.Regular -> None)
      (List.combine vs ctor_info_.binder_kinds)
  in
  let trailing_pattern_names =
    List.filteri (fun i _ -> i > target_pos) aligned_patterns
    |> List.map (function
      | Surface.PVar n -> n
      | Surface.PWildcard -> "_"
      | Surface.PCon _ ->
        Reporter.fatalf
          ~loc:clause_loc
          Elab_error
          "elim: pattern at non-target position must be a variable"
      | Surface.PImpVar _ -> assert false (* normalized away by align_clause_patterns *)
      | Surface.PRecord _ ->
        Reporter.fatalf
          ~loc:clause_loc
          Elab_error
          "elim: record pattern at non-target position must be a variable")
  in
  if List.length trailing_pattern_names <> n_trailing
  then
    Reporter.fatalf
      ~loc:clause_loc
      Elab_error
      "elim clause `%s`: expected %d trailing pattern(s), got %d"
      ctor_name
      n_trailing
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
  { clause_loc; vs; rec_arg_to_ih; trailing_pattern_names; rewritten_body }
;;

(* Qualify bare constructor references in [body] across the scrutinee's
   namespace plus each user-listed `open`. Builds the [shadowed] set from
   the ctor field-binders, IH names, trailing-pattern names, intro names,
   and param names so local bindings always win. *)
let qualify_ctor_namespaces
      ~(clause_loc : Asai.Range.t)
      ~(ind_head : string)
      ~(ctors : (string * int) list)
      ~(opens : string list)
      ~(params : Surface.pretype binder list)
      ~(intros : (string * bool) list)
      ~(vs : string list)
      ~(rec_arg_to_ih : (string * string) list)
      ~(trailing_pattern_names : string list)
      (body : Surface.preterm)
  : Surface.preterm
  =
  let ih_names = List.map snd rec_arg_to_ih in
  let param_names =
    List.map (fun (b : Surface.pretype binder) -> Name.to_string b.name) params
  in
  let intro_names = List.map fst intros in
  let shadowed = vs @ ih_names @ trailing_pattern_names @ intro_names @ param_names in
  let opened_namespaces =
    (ind_head, List.map fst ctors)
    :: List.map
         (fun open_name ->
            let opened_info : Context.ind_info =
              match Context.S.resolve [ open_name ] with
              | Some (_, `Inductive i) -> i
              | _ ->
                Reporter.fatalf
                  ~loc:clause_loc
                  Elab_error
                  "`open %s`: not an inductive"
                  open_name
            in
            open_name, List.map fst (Eliminator_synth.arities_of opened_info))
         opens
  in
  List.fold_left
    (fun body (head, ctor_names) ->
       qualify_ctor_names ~ind_head:head ~ctor_names ~shadowed body)
    body
    opened_namespaces
;;

(* Build the ctor → owner mapping used by [readback_value_to_surface] to
   qualify [Label] values into `Owner/ctor` references that don't depend on
   the scrutinee's auto-open. Seeded with the dep-telescope inductive types'
   ctors followed by the scrutinee's own ctors. *)
let build_owner_map ~(ind_head : string) (info : Context.ind_info)
  : (string * string) list
  =
  let ctors_of (head : string) : (string * string) list =
    match Context.S.resolve [ head ] with
    | Some (_, `Inductive sub_info) ->
      let cnames = List.map fst (Eliminator_synth.arities_of sub_info) in
      List.map (fun c -> c, head) cnames
    | _ -> []
  in
  let from_deps =
    List.concat_map
      (fun (d : Surface.pretype binder) ->
         match head_of_surface d.bound with
         | Surface.Var [ h ] -> ctors_of h
         | _ -> [])
      info.deps
  in
  let from_ind_head = ctors_of ind_head in
  from_deps @ from_ind_head
;;

let cv_of_user_level_names (user_level_names : (int * string) list) : Context_view.t =
  let max_lvl = List.fold_left (fun acc (l, _) -> max acc (l + 1)) 0 user_level_names in
  let names =
    List.init max_lvl (fun l ->
      match List.assoc_opt l user_level_names with
      | Some n -> n
      | None -> "_")
  in
  List.fold_left Context_view.extend Context_view.empty names
;;

let rec core_term_to_surface
          ~(loc : Asai.Range.t)
          ~(cv : Context_view.t)
          ~(owner_map : (string * string) list)
          (t : Core.term)
  : Surface.preterm
  =
  let rb t = core_term_to_surface ~loc ~cv ~owner_map t in
  match t with
  | Core.Universe _ -> Surface.Universe
  | Core.LocalVar ix ->
    let lvl = Context_view.lvl cv - 1 - ix in
    (match Context_view.nth_name_from_lvl cv lvl with
     | Some name -> Surface.Var [ name ]
     | None ->
       Reporter.fatalf
         ~loc
         Elab_error
         "elim: index readback hit unknown local index %d"
         ix)
  | Core.Var n ->
    (match List.assoc_opt n owner_map with
     | Some owner -> Surface.Var [ owner; n ]
     | None -> Surface.Var [ n ])
  | Core.App _ ->
    let rec collect_spine acc = function
      | Core.App (f, a) -> collect_spine (a :: acc) f
      | head -> head, acc
    in
    let head, spine = collect_spine [] t in
    let imps =
      match head with
      | Core.Var x ->
        let ind_imps =
          match Context.S.resolve [ x ] with
          | Some (_, `Inductive info) ->
            let pi = List.map (fun (p : _ Syntax.binder) -> p.implicit) info.params in
            let di = List.map (fun (d : _ Syntax.binder) -> d.implicit) info.deps in
            Some (pi @ di)
          | _ -> None
        in
        let ctor_imps =
          match List.assoc_opt x owner_map with
          | Some owner ->
            (match Context.S.resolve [ owner ] with
             | Some (_, `Inductive info) ->
               let data_imps = List.map (fun _ -> true) info.params in
               let ctor_opt =
                 List.find_opt
                   (fun (c : _ Syntax.binder) -> Syntax.Name.to_string c.name = x)
                   info.ctors
               in
               let binder_imps =
                 match ctor_opt with
                 | Some c ->
                   List.map
                     (fun (b : _ Syntax.binder) -> b.implicit)
                     (Surface.telescope c.bound)
                 | None -> []
               in
               Some (data_imps @ binder_imps)
             | _ -> None)
          | None -> None
        in
        (match ind_imps, ctor_imps with
         | Some imps, _ -> imps
         | _, Some imps -> imps
         | None, None -> [])
      | _ -> []
    in
    let head_s = rb head in
    List.fold_left
      (fun (acc, i) arg ->
         let imp = i < List.length imps && List.nth imps i in
         Surface.App (imp, acc, rb arg), i + 1)
      (head_s, 0)
      spine
    |> fst
  | Core.Lambda { name; bound; implicit } ->
    let ns = Syntax.Name.to_string name in
    let cv' = Context_view.extend cv ns in
    Surface.Lambda
      { name; bound = core_term_to_surface ~loc ~cv:cv' ~owner_map bound; implicit }
  | Core.TypedLambda ({ name; bound; implicit }, body) ->
    let ns = Syntax.Name.to_string name in
    let cv' = Context_view.extend cv ns in
    Surface.TypedLambda
      ( { name; bound = rb bound; implicit }
      , core_term_to_surface ~loc ~cv:cv' ~owner_map body )
  | Core.Pi ({ name; bound; implicit }, body) ->
    let ns = Syntax.Name.to_string name in
    let cv' = Context_view.extend cv ns in
    Surface.Pi
      ( { name; bound = rb bound; implicit }
      , core_term_to_surface ~loc ~cv:cv' ~owner_map body )
  | Core.Meta _ | Core.InsertedMeta _ -> Surface.Hole
  | Core.Lift _ | Core.LiftTerm _ | Core.UnliftTerm _ ->
    Reporter.fatalf
      ~loc
      Elab_error
      "elim: readback can't lower core term `%s` to surface"
      (Pretty.pp_term cv t)
  | Core.RecordType { name = _; params = _; fields = _ } ->
    Reporter.fatalf
      ~loc
      Elab_error
      "elim: readback can't lower core term `%s` to surface"
      (Pretty.pp_term cv t)
  | Core.RecordIntro { name = _; fields } ->
    Surface.RecordLit (List.map (fun (f, e) -> f, rb e) fields)
  | Core.RecordProj { record; field } -> Surface.Proj (rb record, field)
  | Core.IdAbsurd t -> Surface.IdAbsurd (rb t)
;;

let readback_value_to_surface
      ~(loc : Asai.Range.t)
      ~(user_level_names : (int * string) list)
      ~(owner_map : (string * string) list)
      (v : Core.value)
  : Surface.preterm
  =
  let cv = cv_of_user_level_names user_level_names in
  let lvl = Context_view.lvl cv in
  let tm = Evaluation.quote lvl v in
  core_term_to_surface ~loc ~cv ~owner_map tm
;;

let split_target_params_indices
      ~(loc : Asai.Range.t)
      ~(n_total_params : int)
      (target_type_value : Core.value)
  : Core.value list * Core.value list
  =
  match Evaluation.force_head target_type_value with
  | Core.IndType (_, sp) ->
    let xs = Bwd.to_list sp in
    List.filteri (fun i _ -> i < n_total_params) xs, List.drop n_total_params xs
  | other ->
    Reporter.fatalf
      ~loc
      Elab_error
      "elim: target type is not an inductive value, got `%s`"
      (Pretty.pp_term Context_view.empty (Evaluation.quote 0 other))
;;

(* For a constructor, peel its core type past the data params and its own
   field-binders to reach its index spine. Returns the index spine, the flex
   levels assigned to the ctor's fields, and the level→original-binder-name
   map (used later to translate σ back into clause-binder names). *)
let ctor_spine_and_flex
      ~(loc : Asai.Range.t)
      ~(ind_head : string)
      ~(ctor_infos : Context.ctor_info list)
      ~(n_total_params : int)
      ~(target_params : Core.value list)
      ~(start_lvl : int)
      ~(n_intros : int)
      ~(ctor_name : string)
      ~(arity : int)
  : Core.value list * int list * (int * string) list
  =
  let ctor_ty =
    match Context.S.resolve [ ind_head; ctor_name ] with
    | Some (ty, `Constructor) -> ty
    | _ ->
      Reporter.fatalf
        ~loc
        Elab_error
        "elim: cannot find constructor `%s/%s` in context"
        ind_head
        ctor_name
  in
  let after_params =
    List.fold_left
      (fun v arg ->
         match Evaluation.force_head v with
         | Core.VPi (_, k) -> k arg
         | _ ->
           Reporter.fatalf
             ~loc
             Elab_error
             "elim: ctor `%s` has fewer Pi-layers than data params (%d)"
             ctor_name
             n_total_params)
      ctor_ty
      target_params
  in
  let flex_start = start_lvl + n_intros in
  let _used_vals, after_fields = peel_vpi after_params arity flex_start in
  let flex_levels = List.init arity (fun i -> flex_start + i) in
  let ctor_info =
    List.find
      (fun (ci : Context.ctor_info) -> String.equal ci.ctor_name ctor_name)
      ctor_infos
  in
  let flex_name_map =
    List.mapi (fun i name -> flex_start + i, name) ctor_info.binder_names
  in
  let indices =
    match Evaluation.force_head after_fields with
    | Core.IndType (_, sp) ->
      let xs = Bwd.to_list sp in
      List.drop n_total_params xs
    | other ->
      Reporter.fatalf
        ~loc
        Elab_error
        "elim: ctor `%s`'s peeled codomain is not an inductive: `%s`"
        ctor_name
        (Pretty.pp_term Context_view.empty (Evaluation.quote 0 other))
  in
  indices, flex_levels, flex_name_map
;;

(* Per-call-binder implicit flags from a ctor's raw surface signature.
   [info.ctors] stores the user-written ctor type (no [close_ctor_type] wrap),
   so all Pi-binders here are per-call. *)
let ctor_binder_implicits (info : Context.ind_info) (ctor_name : string) : bool list =
  let ctor_surface =
    List.find (fun (b : Surface.pretype binder) -> b.name = Named ctor_name) info.ctors
  in
  List.map (fun (b : Surface.pretype binder) -> b.implicit) (pi_domain ctor_surface.bound)
;;

(* Build the unify-path motive. When [has_conflict] is set, the motive is
   Id-reified — one `p_k : Id T_k idx_k actual_k` Pi-binder per index — so
   Conflict cases can discharge their unreachable witness via [\absurd-id].
   All-Success calls leave the witnesses out. *)
let build_unify_motive
      ~(loc : Asai.Range.t)
      ~(np : int)
      ~(target_pos : int)
      ~(signature : Surface.pretype)
      ~(target : string)
      ~(has_conflict : bool)
      ~(m_indices : int)
      ~(idx_name : int -> string)
      ~(p_name : int -> string)
      ~(target_index_surfaces : Surface.preterm list)
  : Surface.preterm
  =
  let result_after_target = peel_pi_surface ~loc (target_pos - np + 1) signature in
  let with_ids =
    if has_conflict
    then (
      let rec wrap_ids i acc =
        if i < 0
        then acc
        else (
          let id_ty =
            Surface.apply
              (Surface.Var [ "Id" ])
              [ Surface.Var [ idx_name i ]; List.nth target_index_surfaces i ]
          in
          wrap_ids
            (i - 1)
            (Surface.Pi ({ name = Named (p_name i); bound = id_ty; implicit = false }, acc)))
      in
      wrap_ids (m_indices - 1) result_after_target)
    else result_after_target
  in
  let inner =
    Surface.Lambda { name = Named target; bound = with_ids; implicit = false }
  in
  let rec wrap_idx_lambdas i acc =
    if i < 0
    then acc
    else
      wrap_idx_lambdas
        (i - 1)
        (Surface.Lambda { name = Named (idx_name i); bound = acc; implicit = false })
  in
  wrap_idx_lambdas (m_indices - 1) inner
;;

(* Wrap [body] with one Pi-binder per Id-witness when [has_conflict]; identity
   otherwise. Mirrors the witness-binder structure of [build_unify_motive]. *)
let wrap_p_binders
      ~(has_conflict : bool)
      ~(m_indices : int)
      ~(p_name : int -> string)
      (body : Surface.preterm)
  : Surface.preterm
  =
  if not has_conflict
  then body
  else (
    let rec go i acc =
      if i < 0
      then acc
      else
        go
          (i - 1)
          (Surface.Lambda { name = Named (p_name i); bound = acc; implicit = false })
    in
    go (m_indices - 1) body)
;;

(* The non-variable-index path for [build_elim_body], driven by the
   first-order index unifier in [Index_unify]. Called when at least one
   index in the target's type is not a bare variable; otherwise the
   existing renaming-based path in [build_elim_body] is used.

   This path always builds an Id-reified motive: for each index k, the
   motive takes an extra `(p_k : Id T_k idx_var_k actual_k)` argument. At
   the elim call site we pass `refl` for each `p_k`. *)
let build_elim_body_unify
      ~(loc : Asai.Range.t)
      ~(func_name : string)
      ~(params : Surface.pretype binder list)
      ~(signature : Surface.pretype)
      ~(opens : string list)
      ~(intros : (string * bool) list)
      ~(target : string)
      ~(target_pos : int)
      ~(np : int)
      ~(n_intros : int)
      ~(ind_head : string)
      ~(data_args : Surface.preterm list)
      ~(info : Context.ind_info)
      ~(ctors : (string * int) list)
      ~(ctor_infos : Context.ctor_info list)
      ~(clauses : Surface.clause list)
      ~(target_type_value : Core.value)
      ~(start_lvl : int)
  : Surface.preterm
  =
  let intro_names = List.map fst intros in
  let user_level_names : (int * string) list =
    List.mapi (fun i name -> start_lvl + i, name) intro_names
  in
  let n_total_params = List.length info.params in
  let owner_map = build_owner_map ~ind_head info in
  let readback_v = readback_value_to_surface ~loc ~user_level_names ~owner_map in
  let target_params, target_indices =
    split_target_params_indices ~loc ~n_total_params target_type_value
  in
  let ctor_outcomes
    : (string * int * bool list * Index_unify.outcome * (int * string) list) list
    =
    List.map
      (fun (ctor_name, arity) ->
         let ctor_idx, flex_levels, flex_name_map =
           ctor_spine_and_flex
             ~loc
             ~ind_head
             ~ctor_infos
             ~n_total_params
             ~target_params
             ~start_lvl
             ~n_intros
             ~ctor_name
             ~arity
         in
         let outcome =
           Index_unify.unify ~flex:flex_levels ~lhs:ctor_idx ~rhs:target_indices
         in
         let implicits = ctor_binder_implicits info ctor_name in
         ctor_name, arity, implicits, outcome, flex_name_map)
      ctors
  in
  (* Fail Stuck cases up front so the error mentions which ctor was stuck. *)
  List.iter
    (fun (ctor_name, _, _, o, _) ->
       match o with
       | Index_unify.Stuck s ->
         Reporter.fatalf
           ~loc
           Elab_error
           "elim: cannot determine the %dth index for ctor `%s` — unifier got stuck on \
            `%s` ≟ `%s`"
           s.position
           ctor_name
           (Pretty.pp_term Context_view.empty (Evaluation.quote 0 s.lhs))
           (Pretty.pp_term Context_view.empty (Evaluation.quote 0 s.rhs))
       | _ -> ())
    ctor_outcomes;
  let normalize_pattern = make_normalize ctors in
  let m_indices = List.length target_indices in
  let elim_freshener = make_freshener intro_names in
  let idx_names_arr = Array.init m_indices (fun _ -> elim_freshener.freshen "i") in
  let p_names_arr = Array.init m_indices (fun _ -> elim_freshener.freshen "p") in
  let idx_name i = idx_names_arr.(i) in
  let p_name i = p_names_arr.(i) in
  let has_conflict =
    List.exists
      (fun (_, _, _, o, _) ->
         match o with
         | Index_unify.Conflict _ -> true
         | _ -> false)
      ctor_outcomes
  in
  (* Read the target's actual index values back into surface so the Id-reified
     motive can mention them. Used only when [has_conflict] triggers
     Id-reification; for the all-Success path the simpler motive captures
     user intros by name and doesn't need this. *)
  let target_index_surfaces : Surface.preterm list =
    if has_conflict then List.map readback_v target_indices else []
  in
  let motive =
    build_unify_motive
      ~loc
      ~np
      ~target_pos
      ~signature
      ~target
      ~has_conflict
      ~m_indices
      ~idx_name
      ~p_name
      ~target_index_surfaces
  in
  let wrap_p_binders body = wrap_p_binders ~has_conflict ~m_indices ~p_name body in
  let trailing_intros = List.filteri (fun i _ -> i > target_pos) intros in
  let case_args : Surface.preterm list =
    List.map
      (fun (ctor_name, arity, implicits, outcome, flex_name_map) ->
         let ctor_info_ =
           List.find
             (fun (i : Context.ctor_info) -> String.equal i.ctor_name ctor_name)
             ctor_infos
         in
         let close_ctor_lambdas ~check_loc names body =
           if List.length names <> List.length implicits
           then
             Reporter.fatalf
               ~loc:check_loc
               Elab_error
               "elim: ctor `%s` binder/implicit length mismatch (%d vs %d)"
               ctor_name
               (List.length names)
               (List.length implicits);
           let binders =
             List.combine (List.combine names ctor_info_.binder_kinds) implicits
           in
           List.fold_right
             (fun ((v, kind), implicit) body ->
                let inner =
                  match (kind : Context.binder_kind) with
                  | Context.Recursive _ ->
                    Surface.Lambda
                      { name = Named (func_name ^ " " ^ v)
                      ; bound = body
                      ; implicit = false
                      }
                  | Context.Regular -> body
                in
                Surface.Lambda { name = Named v; bound = inner; implicit })
             binders
             body
         in
         let matched_clauses =
           find_matched_clauses_for_ctor
             ~loc
             ~intros
             ~target_pos
             ~normalize_pattern
             ~ctor_name
             clauses
         in
         let opt_clause =
           match
             pick_head_and_deeper
               ~loc
               ~intros
               ~target_pos
               ~normalize_pattern
               matched_clauses
           with
           | Some (h, _) -> Some h
           | None -> List.nth_opt matched_clauses 0
         in
         match outcome with
         | Index_unify.Conflict { position = k; lhs; rhs } ->
           (* The user must NOT have written a clause for an unreachable
              case (clearer error than the missing-clause check below). *)
           (match opt_clause with
            | Some _ ->
              Reporter.fatalf
                ~loc
                Elab_error
                "elim on `%s`: ctor `%s`'s index disagrees with target's at position %d \
                 (`%s` vs `%s`), so this case is unreachable; remove the clause"
                ind_head
                ctor_name
                k
                (Pretty.pp_term
                   Context_view.empty
                   (Evaluation.quote (Context_view.lvl Context_view.empty) lhs))
                (Pretty.pp_term
                   Context_view.empty
                   (Evaluation.quote (Context_view.lvl Context_view.empty) rhs))
            | None -> ());
           (* Auto-remove: the case's `p_k : Id T_k idx_k actual_k` has
              orthogonal ctor heads on both sides, so `\absurd-id` derives
              `Empty` and `absurd` casts it to the case body's type. *)
           let absurd_body =
             Surface.App
               ( false
               , Surface.Var [ "absurd" ]
               , Surface.IdAbsurd (Surface.Var [ p_name k ]) )
           in
           close_ctor_lambdas
             ~check_loc:loc
             ctor_info_.binder_names
             (wrap_p_binders absurd_body)
         | Index_unify.Success sigma ->
           let clause =
             match opt_clause with
             | Some c -> c
             | None ->
               Reporter.fatalf
                 ~loc
                 Elab_error
                 "elim on `%s`: no clause for constructor `%s`"
                 ind_head
                 ctor_name
           in
           let pc =
             process_clause
               ~loc
               ~func_name
               ~ctor_name
               ~arity
               ~implicits
               ~ctor_info_
               ~intros
               ~target_pos
               ~n_intros
               ~n_trailing:(List.length trailing_intros)
               ~normalize_pattern
               clause
           in
           (* Apply σ as a substitution: ctor field-binder name → surface
              readback of the σ value. Index_unify's σ maps ctor flex levels
              to values; the flex_name_map maps levels back to the original
              ctor binder names, and the user may have renamed those via
              `cons {m} x xs` syntax (recorded in `pc.vs`). *)
           let body_after_sigma =
             let sigma_renamings : (string * Surface.preterm) list =
               List.filter_map
                 (fun (lvl, v) ->
                    match List.assoc_opt lvl flex_name_map with
                    | None -> None
                    | Some orig_name ->
                      let user_name =
                        try
                          List.assoc
                            orig_name
                            (List.combine ctor_info_.binder_names pc.vs)
                        with
                        | Not_found -> orig_name
                      in
                      Some (user_name, readback_v v))
                 sigma
             in
             subst_vars_surface sigma_renamings pc.rewritten_body
           in
           let body_with_siblings =
             match body_after_sigma with
             | Surface.Inline_elim d when List.length matched_clauses > 1 ->
               let siblings =
                 make_siblings_with_views
                   ~loc
                   ~intros
                   ~target_pos
                   ~normalize_pattern
                   ~ctor_name
                   ~implicits
                   ~binder_names:ctor_info_.binder_names
                   matched_clauses
               in
               Surface.Inline_elim
                 { d with siblings; outer_subst = sigma @ d.outer_subst }
             | _ -> body_after_sigma
           in
           let qualified_body =
             qualify_ctor_namespaces
               ~clause_loc:pc.clause_loc
               ~ind_head
               ~ctors
               ~opens
               ~params
               ~intros
               ~vs:pc.vs
               ~rec_arg_to_ih:pc.rec_arg_to_ih
               ~trailing_pattern_names:pc.trailing_pattern_names
               body_with_siblings
           in
           let with_trailing =
             List.fold_right
               (fun n body ->
                  Surface.Lambda { name = Named n; bound = body; implicit = false })
               pc.trailing_pattern_names
               qualified_body
           in
           let with_p = wrap_p_binders with_trailing in
           close_ctor_lambdas ~check_loc:pc.clause_loc pc.vs with_p
         | Index_unify.Stuck _ -> assert false (* already handled above *))
      ctor_outcomes
  in
  let elim_call =
    let refl_args =
      if has_conflict
      then List.init m_indices (fun _ -> Surface.Var [ "Id"; "refl" ])
      else []
    in
    List.fold_left
      (fun acc a -> Surface.App (false, acc, a))
      (Surface.Var [ ind_head; "elim" ])
      (data_args @ [ Surface.Var [ target ]; motive ] @ case_args @ refl_args)
  in
  List.fold_left
    (fun acc (n, _) -> Surface.App (false, acc, Surface.Var [ n ]))
    elim_call
    trailing_intros
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
   `signature`'s Pi tower past the target as a function of the target.

   When the target's type has any non-variable index, this function takes
   the index-unification path: it consults `target_type_value` and runs
   the first-order unifier from [Index_unify] per constructor. *)
let build_elim_body
      ~(loc : Asai.Range.t)
      ~(func_name : string)
      ~(params : Surface.pretype binder list)
      ~(signature : Surface.pretype)
      ~(opens : string list)
      ~(intros : (string * bool) list)
      ~(target : string)
      ~(clauses : Surface.clause list)
      ~(target_type_value : Core.value)
      ~(start_lvl : int)
  : Surface.preterm
  =
  let intros = compute_effective_intros ~loc ~bindings:params ~signature ~intros in
  let np = List.length params in
  let n_intros = List.length intros in
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
    go 0 intros
  in
  (* Target's Pi-binder is at position (target_pos - np) in `signature`
     (signature has only the past-params Pi-layers). Take its domain — the
     target's type — as a Surface term. *)
  let target_type_surface : Surface.pretype =
    match List.nth_opt (pi_domain signature) (target_pos - np) with
    | Some b -> b.bound
    | None ->
      Reporter.fatalf ~loc Elab_error "elim: signature has fewer Pi-layers than required"
  in
  let ind_head, data_args =
    let here = loc_or loc target_type_surface in
    match head_of_surface target_type_surface with
    | Surface.Var [ n ] -> n, Surface.applied_spine target_type_surface
    | Surface.Var _ ->
      Reporter.fatalf
        ~loc:here
        Elab_error
        "elim: target's type head must be a bare inductive name"
    | _ ->
      Reporter.fatalf ~loc:here Elab_error "elim: target's type head is not an inductive"
  in
  let info : Context.ind_info =
    match Context.S.resolve [ ind_head ] with
    | Some (_, `Inductive info) -> info
    | _ -> Reporter.fatalf ~loc Elab_error "elim: `%s` is not an inductive" ind_head
  in
  let ctors = Eliminator_synth.arities_of info in
  let ctor_infos = info.infos in
  let normalize_pattern = make_normalize ctors in
  (* Index args of the target's type: the spine entries past the explicit
     params correspond to the inductive's dep telescope. The motive must
     abstract over those, then over the target itself. For each index given
     as a Var `v`, bind a fresh name and rename `v -> fresh` in the body. *)
  let n_explicit_params =
    List.length
      (List.filter (fun (p : Surface.pretype binder) -> not p.implicit) info.params)
  in
  let dep_args = List.drop n_explicit_params data_args in
  let n_deps = List.length info.deps in
  if List.length dep_args <> n_deps
  then
    Reporter.fatalf
      ~loc
      Elab_error
      "elim: target type spine has %d index arg(s), expected %d"
      (List.length dep_args)
      n_deps;
  let rec strip_loc = function
    | Surface.Located { value; _ } -> strip_loc value
    | t -> t
  in
  let any_non_var =
    List.exists
      (fun a ->
         match strip_loc a with
         | Surface.Var [ _ ] -> false
         | _ -> true)
      dep_args
  in
  if any_non_var
  then
    build_elim_body_unify
      ~loc
      ~func_name
      ~params
      ~signature
      ~opens
      ~intros
      ~target
      ~target_pos
      ~np
      ~n_intros
      ~ind_head
      ~data_args
      ~info
      ~ctors
      ~ctor_infos
      ~clauses
      ~target_type_value
      ~start_lvl
  else (
    let intro_names = List.map fst intros in
    let dep_freshener = make_freshener intro_names in
    let dep_renaming : (string * string) list =
      List.map
        (fun a ->
           match strip_loc a with
           | Surface.Var [ n ] -> n, dep_freshener.freshen "i"
           | _ ->
             Reporter.fatalf
               ~loc
               Elab_error
               "INTERNAL BUG: elim dep_arg not a bare Var after any_non_var=false guard; \
                please report this bug")
        dep_args
    in
    let motive : Surface.preterm =
      let body0 = peel_pi_surface ~loc (target_pos - np + 1) signature in
      let body = rename_vars_surface dep_renaming body0 in
      let inner =
        Surface.Lambda { name = Named target; bound = body; implicit = false }
      in
      List.fold_right
        (fun (_, fresh) acc ->
           Surface.Lambda { name = Named fresh; bound = acc; implicit = false })
        dep_renaming
        inner
    in
    let trailing_intros = List.filteri (fun i _ -> i > target_pos) intros in
    let case_args : Surface.preterm list =
      List.map
        (fun (ctor_name, arity) ->
           let ctor_info_ =
             List.find
               (fun (i : Context.ctor_info) -> String.equal i.ctor_name ctor_name)
               ctor_infos
           in
           let matched_clauses =
             find_matched_clauses_for_ctor
               ~loc
               ~intros
               ~target_pos
               ~normalize_pattern
               ~ctor_name
               clauses
           in
           let clause =
             match
               pick_head_and_deeper
                 ~loc
                 ~intros
                 ~target_pos
                 ~normalize_pattern
                 matched_clauses
             with
             | Some (h, _) -> h
             | None ->
               (match matched_clauses with
                | c :: _ -> c
                | [] ->
                  Reporter.fatalf
                    ~loc
                    Elab_error
                    "elim on `%s`: no clause for constructor `%s`"
                    ind_head
                    ctor_name)
           in
           let implicits = ctor_binder_implicits info ctor_name in
           let pc =
             process_clause
               ~loc
               ~func_name
               ~ctor_name
               ~arity
               ~implicits
               ~ctor_info_
               ~intros
               ~target_pos
               ~n_intros
               ~n_trailing:(List.length trailing_intros)
               ~normalize_pattern
               clause
           in
           let body_with_siblings =
             if List.length matched_clauses > 1
             then (
               let siblings =
                 make_siblings_with_views
                   ~loc
                   ~intros
                   ~target_pos
                   ~normalize_pattern
                   ~ctor_name
                   ~implicits
                   ~binder_names:ctor_info_.binder_names
                   matched_clauses
               in
               annotate_inline_elim_siblings pc.rewritten_body siblings)
             else pc.rewritten_body
           in
           let qualified_body =
             qualify_ctor_namespaces
               ~clause_loc:pc.clause_loc
               ~ind_head
               ~ctors
               ~opens
               ~params
               ~intros
               ~vs:pc.vs
               ~rec_arg_to_ih:pc.rec_arg_to_ih
               ~trailing_pattern_names:pc.trailing_pattern_names
               body_with_siblings
           in
           let with_trailing =
             List.fold_right
               (fun n body ->
                  Surface.Lambda { name = Named n; bound = body; implicit = false })
               pc.trailing_pattern_names
               qualified_body
           in
           List.fold_right
             (fun ((v, kind), implicit) body ->
                let inner =
                  match (kind : Context.binder_kind) with
                  | Context.Recursive _ ->
                    Surface.Lambda
                      { name = Named (func_name ^ " " ^ v)
                      ; bound = body
                      ; implicit = false
                      }
                  | Context.Regular -> body
                in
                Surface.Lambda { name = Named v; bound = inner; implicit })
             (List.combine (List.combine pc.vs ctor_info_.binder_kinds) implicits)
             with_trailing)
        ctors
    in
    let elim_call =
      List.fold_left
        (fun acc a -> Surface.App (false, acc, a))
        (Surface.Var [ ind_head; "elim" ])
        (data_args @ [ Surface.Var [ target ]; motive ] @ case_args)
    in
    List.fold_left
      (fun acc (n, _) -> Surface.App (false, acc, Surface.Var [ n ]))
      elim_call
      trailing_intros)
;;

let find_var_in_spine ~(name : string) (spine : Surface.preterm list)
  : (int * (string * int) option) option
  =
  let strip = function
    | Surface.Located { value; _ } -> value
    | t -> t
  in
  let is_named p =
    match strip p with
    | Surface.Var [ n ] when String.equal n name -> true
    | _ -> false
  in
  let rec walk i = function
    | [] -> None
    | elem :: rest ->
      if is_named elem
      then Some (i, None)
      else (
        let head, args = head_and_spine (strip elem) in
        match strip head with
        | Surface.Var path when args <> [] ->
          let ctor_name =
            match List.rev path with
            | leaf :: _ -> leaf
            | [] -> ""
          in
          let rec sub j = function
            | [] -> None
            | a :: arest -> if is_named a then Some j else sub (j + 1) arest
          in
          (match sub 0 args with
           | Some j -> Some (i, Some (ctor_name, j))
           | None -> walk (i + 1) rest)
        | _ -> walk (i + 1) rest)
  in
  walk 0 spine
;;

let build_cong_extractor
      ~(dep_binder_idx : int)
      ~(sub_opt : (string * int) option)
      ~(info : Context.ind_info)
  : Surface.preterm option
  =
  match sub_opt with
  | None -> Some (Surface.lambda [ "__sh" ] (Surface.Var [ "__sh" ]))
  | Some (matched_ctor_name, sub_arg_idx) ->
    let dep_binder = List.nth info.deps dep_binder_idx in
    (match head_of_surface dep_binder.Syntax.bound with
     | Surface.Var [ index_ind_name ] ->
       (match Context.S.resolve [ index_ind_name ] with
        | Some (_, `Inductive index_info) ->
          let cases =
            List.map
              (fun (c : Surface.pretype binder) ->
                 let lambdas, fields =
                   Eliminator_synth.case_arg_lambda_binders
                     ~prefix:""
                     ~ind_name:index_ind_name
                     c
                 in
                 if c.name = Named matched_ctor_name && sub_arg_idx < List.length fields
                 then Surface.lambda lambdas (Surface.Var [ List.nth fields sub_arg_idx ])
                 else (
                   let default_ctor =
                     match Eliminator_synth.arities_of index_info with
                     | (n, _) :: _ -> Surface.Var [ index_ind_name; n ]
                     | [] -> Surface.Var [ "__sh" ]
                   in
                   Surface.lambda lambdas default_ctor))
              index_info.ctors
          in
          let motive =
            Surface.Lambda
              { name = Anon; bound = Surface.Var [ index_ind_name ]; implicit = false }
          in
          Some
            (Surface.Lambda
               { name = Named "__sh"
               ; bound =
                   Surface.apply
                     (Surface.Var [ index_ind_name; "elim" ])
                     ([ Surface.Var [ "__sh" ]; motive ] @ cases)
               ; implicit = false
               })
        | _ -> None)
     | _ -> None)
;;

let position_of_target
      ~(loc : Asai.Range.t)
      ~(target_name : string)
      ~(head_view : Surface.pattern list)
  : int
  =
  let rec go i = function
    | [] ->
      Reporter.fatalf
        ~loc
        Elab_error
        "nested `<= \\elim %s`: target not found among current binders"
        target_name
    | Surface.PVar n :: _ when String.equal n target_name -> i
    | Surface.PImpVar n :: _ when String.equal n target_name -> i
    | _ :: rest -> go (i + 1) rest
  in
  go 0 head_view
;;

let build_inline_elim_dispatch
      ~(loc : Asai.Range.t)
      ~(target_name : string)
      ~(target_type_raw : Core.value)
      ~(target_type_value : Core.value)
      ~(siblings : (Surface.clause * Surface.pattern list) list)
      ~(result_type_surface : Surface.preterm)
      ~(start_lvl : int)
      ~(user_level_names : (int * string) list)
      ~(outer_subst : (int * Core.value) list)
      ~(target_override : Surface.preterm option)
  : Surface.preterm
  =
  let head_view =
    match siblings with
    | (_, v) :: _ -> v
    | [] ->
      Reporter.fatalf
        ~loc
        Elab_error
        "nested `<= \\elim %s`: no siblings recorded; this is an internal bug"
        target_name
  in
  let target_pos = position_of_target ~loc ~target_name ~head_view in
  let ind_head, target_full_spine =
    match Evaluation.force_head target_type_value with
    | Core.IndType (n, sp) -> n, Bwd.to_list sp
    | other ->
      Reporter.fatalf
        ~loc
        Elab_error
        "nested `<= \\elim %s`: target's type is not an inductive, got `%s`"
        target_name
        (Pretty.pp_term Context_view.empty (Evaluation.quote 0 other))
  in
  let info : Context.ind_info =
    match Context.S.resolve [ ind_head ] with
    | Some (_, `Inductive i) -> i
    | _ ->
      Reporter.fatalf
        ~loc
        Elab_error
        "nested `<= \\elim %s`: `%s` is not an inductive"
        target_name
        ind_head
  in
  let ctors = Eliminator_synth.arities_of info in
  let ctor_infos = info.infos in
  let n_total_params = List.length info.params in
  let target_params, target_indices =
    split_target_params_indices ~loc ~n_total_params target_type_value
  in
  let owner_map = build_owner_map ~ind_head info in
  let readback_v = readback_value_to_surface ~loc ~user_level_names ~owner_map in
  let normalize_pattern = make_normalize ctors in
  let ctor_outcomes
    : (string * int * bool list * Index_unify.outcome * (int * string) list) list
    =
    List.map
      (fun (ctor_name, arity) ->
         let ctor_idx, flex_levels, flex_name_map =
           ctor_spine_and_flex
             ~loc
             ~ind_head
             ~ctor_infos
             ~n_total_params
             ~target_params
             ~start_lvl
             ~n_intros:0
             ~ctor_name
             ~arity
         in
         let outcome =
           Index_unify.unify ~flex:flex_levels ~lhs:ctor_idx ~rhs:target_indices
         in
         let implicits = ctor_binder_implicits info ctor_name in
         ctor_name, arity, implicits, outcome, flex_name_map)
      ctors
  in
  List.iter
    (fun (ctor_name, _, _, o, _) ->
       match o with
       | Index_unify.Stuck s ->
         Reporter.fatalf
           ~loc
           Elab_error
           "nested `<= \\elim %s`: cannot determine the %dth index for ctor `%s` — \
            unifier got stuck on `%s` ≟ `%s`"
           target_name
           s.position
           ctor_name
           (Pretty.pp_term Context_view.empty (Evaluation.quote 0 s.lhs))
           (Pretty.pp_term Context_view.empty (Evaluation.quote 0 s.rhs))
       | _ -> ())
    ctor_outcomes;
  let m_indices = List.length target_indices in
  let outer_scope_names = List.map snd user_level_names in
  let motive_freshener = make_freshener outer_scope_names in
  let idx_names_arr = Array.init m_indices (fun _ -> motive_freshener.freshen "i") in
  let p_names_arr = Array.init m_indices (fun _ -> motive_freshener.freshen "p") in
  let idx_name i = idx_names_arr.(i) in
  let p_name i = p_names_arr.(i) in
  let post_motive_scope =
    outer_scope_names @ Array.to_list p_names_arr @ Array.to_list idx_names_arr
  in
  let id_reify = outer_subst = [] in
  let target_index_surfaces : Surface.preterm list =
    if id_reify then List.map readback_v target_indices else []
  in
  let motive : Surface.preterm =
    let with_ids =
      if id_reify
      then (
        let rec wrap_ids i acc =
          if i < 0
          then acc
          else (
            let id_ty =
              Surface.apply
                (Surface.Var [ "Id" ])
                [ Surface.Var [ idx_name i ]; List.nth target_index_surfaces i ]
            in
            wrap_ids
              (i - 1)
              (Surface.Pi
                 ({ name = Named (p_name i); bound = id_ty; implicit = false }, acc)))
        in
        wrap_ids (m_indices - 1) result_type_surface)
      else result_type_surface
    in
    let inner =
      Surface.Lambda { name = Named target_name; bound = with_ids; implicit = false }
    in
    let rec wrap_idx_lambdas i acc =
      if i < 0
      then acc
      else
        wrap_idx_lambdas
          (i - 1)
          (Surface.Lambda { name = Named (idx_name i); bound = acc; implicit = false })
    in
    wrap_idx_lambdas (m_indices - 1) inner
  in
  let wrap_p_binders body =
    wrap_p_binders ~has_conflict:id_reify ~m_indices ~p_name body
  in
  let case_args : Surface.preterm list =
    List.map
      (fun (ctor_name, _arity, implicits, outcome, flex_name_map) ->
         let ctor_info_ =
           List.find
             (fun (i : Context.ctor_info) -> String.equal i.ctor_name ctor_name)
             ctor_infos
         in
         let close_ctor_lambdas ~check_loc names body =
           if List.length names <> List.length implicits
           then
             Reporter.fatalf
               ~loc:check_loc
               Elab_error
               "nested `<= \\elim`: ctor `%s` binder/implicit length mismatch (%d vs %d)"
               ctor_name
               (List.length names)
               (List.length implicits);
           let binders =
             List.combine (List.combine names ctor_info_.binder_kinds) implicits
           in
           List.fold_right
             (fun ((v, kind), implicit) body ->
                let inner =
                  match (kind : Context.binder_kind) with
                  | Context.Recursive _ ->
                    Surface.Lambda
                      { name = Named ("ih-" ^ v); bound = body; implicit = false }
                  | Context.Regular -> body
                in
                Surface.Lambda { name = Named v; bound = inner; implicit })
             binders
             body
         in
         let matched_sub =
           List.filter
             (fun (_, view) ->
                match Option.map normalize_pattern (List.nth_opt view target_pos) with
                | Some (Surface.PCon (cn, _)) -> String.equal cn ctor_name
                | _ -> false)
             siblings
         in
         match outcome with
         | Index_unify.Conflict { position = k; _ } as outcome_conflict ->
           let _ = outcome_conflict in
           if matched_sub <> []
           then
             Reporter.fatalf
               ~loc
               Elab_error
               "nested `<= \\elim`: ctor `%s`'s index disagrees with the target's, so \
                this case is unreachable; remove the clause"
               ctor_name;
           let body =
             if id_reify
             then
               Surface.App
                 ( false
                 , Surface.Var [ "absurd" ]
                 , Surface.IdAbsurd (Surface.Var [ p_name k ]) )
             else Surface.Hole
           in
           close_ctor_lambdas ~check_loc:loc ctor_info_.binder_names (wrap_p_binders body)
         | Index_unify.Success sigma ->
           let sub_head_view =
             match matched_sub with
             | [] ->
               Reporter.fatalf
                 ~loc
                 Elab_error
                 "nested `<= \\elim`: no clause for constructor `%s/%s`"
                 ind_head
                 ctor_name
             | _ ->
               let is_pvar = function
                 | Surface.PVar _ | Surface.PImpVar _ | Surface.PWildcard -> true
                 | Surface.PCon _ | Surface.PRecord _ -> false
               in
               let head_opt =
                 List.find_opt
                   (fun (_, view) ->
                      match
                        Option.map normalize_pattern (List.nth_opt view target_pos)
                      with
                      | Some (Surface.PCon (_, sps)) -> List.for_all is_pvar sps
                      | _ -> false)
                   matched_sub
               in
               (match head_opt with
                | Some hv -> hv
                | None ->
                  Reporter.fatalf
                    ~loc
                    Elab_error
                    "nested `<= \\elim`: no leaf clause for ctor `%s` — every matching \
                     clause carries a deeper PCon at the dispatched position; add a \
                     parent clause with a bare ctor pattern"
                    ctor_name)
           in
           let sub_head, sub_head_view = sub_head_view in
           let head_sub_pats =
             match
               Option.map normalize_pattern (List.nth_opt sub_head_view target_pos)
             with
             | Some (Surface.PCon (_, sps)) -> sps
             | _ -> []
           in
           let vs : string list =
             List.map
               (function
                 | Surface.PVar n -> n
                 | Surface.PImpVar n -> n
                 | Surface.PWildcard -> "_"
                 | Surface.PCon _ ->
                   Reporter.fatalf
                     ~loc
                     Elab_error
                     "nested `<= \\elim`: head sibling's PCon sub-pattern was not a \
                      variable — internal invariant violated"
                 | Surface.PRecord _ ->
                   Reporter.fatalf
                     ~loc
                     Elab_error
                     "nested `<= \\elim`: record pattern not allowed inside a ctor")
               head_sub_pats
           in
           let vs =
             expand_pattern_binders
               ~loc
               ~ctor_name
               ~implicits
               ~binder_names:ctor_info_.binder_names
               vs
           in
           let case_freshener = make_freshener post_motive_scope in
           let rename_auto_implicit (orig : string) (user_pat : Surface.pattern option)
             : string
             =
             let user_wrote_it =
               match user_pat with
               | Some (Surface.PVar _) | Some (Surface.PImpVar _) -> true
               | _ -> false
             in
             if user_wrote_it
             then (
               case_freshener.claim orig;
               orig)
             else case_freshener.freshen orig
           in
           let head_sub_pats_aligned =
             let n_user = List.length head_sub_pats in
             let n_total = List.length vs in
             if n_user = n_total
             then List.map (fun p -> Some p) head_sub_pats
             else (
               let rec go names imps user =
                 match names, imps, user with
                 | [], [], [] -> []
                 | _ :: rest_n, true :: rest_i, _ -> None :: go rest_n rest_i user
                 | _ :: rest_n, false :: rest_i, p :: rest_p ->
                   Some p :: go rest_n rest_i rest_p
                 | _ -> assert false
               in
               go ctor_info_.binder_names implicits head_sub_pats)
           in
           let vs =
             List.map2
               (fun v user_pat -> rename_auto_implicit v user_pat)
               vs
               head_sub_pats_aligned
           in
           let sigma_renamings : (string * Surface.preterm) list =
             List.filter_map
               (fun (lvl, v) ->
                  match List.assoc_opt lvl flex_name_map with
                  | None -> None
                  | Some orig_name ->
                    let user_name =
                      try
                        List.assoc orig_name (List.combine ctor_info_.binder_names vs)
                      with
                      | Not_found -> orig_name
                    in
                    Some (user_name, readback_v v))
               sigma
           in
           let new_siblings_for_next =
             List.map
               (fun (c, view) ->
                  let sps =
                    match Option.map normalize_pattern (List.nth_opt view target_pos) with
                    | Some (Surface.PCon (_, sps)) -> sps
                    | _ -> []
                  in
                  let expanded =
                    expand_pcon_sub_patterns
                      ~loc:(loc_or loc c.Surface.body)
                      ~ctor_name
                      ~implicits
                      ~binder_names:ctor_info_.binder_names
                      sps
                  in
                  let new_view =
                    update_view_after_ctor_match ~view ~target_pos ~expanded
                  in
                  c, new_view)
               matched_sub
           in
           let coerce_wraps =
             if id_reify
             then (
               let n_explicit_params =
                 List.length
                   (List.filter
                      (fun (p : Surface.pretype binder) -> not p.implicit)
                      info.params)
               in
               let outer_ctor =
                 List.find
                   (fun (c : Surface.pretype binder) -> c.name = Named ctor_name)
                   info.ctors
               in
               let cod_spine =
                 List.drop
                   n_explicit_params
                   (Surface.applied_spine (Surface.codomain outer_ctor.bound))
               in
               List.filter_map
                 (fun (i, kind) ->
                    match (kind : Context.binder_kind) with
                    | Context.Regular -> None
                    | Context.Recursive dep_names ->
                      let bind_user_name = List.nth vs i in
                      let coerce =
                        List.find_map
                          (fun dep_name ->
                             match
                               List.find_opt
                                 (fun (_, n) -> String.equal n dep_name)
                                 flex_name_map
                             with
                             | Some (lvl, _) ->
                               (match List.assoc_opt lvl sigma with
                                | None -> None
                                | Some value -> Some (dep_name, value, readback_v value))
                             | None -> None)
                          dep_names
                      in
                      (match coerce with
                       | None -> None
                       | Some (dep_name, _value, value_surface) ->
                         (match find_var_in_spine ~name:dep_name cod_spine with
                          | None -> None
                          | Some (spine_idx, sub_opt) ->
                            let extractor =
                              build_cong_extractor
                                ~dep_binder_idx:spine_idx
                                ~sub_opt
                                ~info
                            in
                            (match extractor with
                             | None -> None
                             | Some extr ->
                               let dep_pos_opt =
                                 List.find_index
                                   (fun n -> String.equal n dep_name)
                                   ctor_info_.binder_names
                               in
                               (match dep_pos_opt with
                                | None -> None
                                | Some dep_pos ->
                                  let dep_user_name = List.nth vs dep_pos in
                                  let rename_subst : (string * Surface.preterm) list =
                                    List.map2
                                      (fun bn uv -> bn, Surface.Var [ uv ])
                                      ctor_info_.binder_names
                                      vs
                                  in
                                  let cons_idx_lhs =
                                    subst_vars_surface
                                      rename_subst
                                      (List.nth cod_spine spine_idx)
                                  in
                                  let cons_idx_rhs =
                                    List.nth target_index_surfaces spine_idx
                                  in
                                  let cong_proof =
                                    Surface.App
                                      ( false
                                      , Surface.App
                                          ( true
                                          , Surface.App
                                              ( true
                                              , Surface.App
                                                  (false, Surface.Var [ "cong" ], extr)
                                              , cons_idx_lhs )
                                          , cons_idx_rhs )
                                      , Surface.Var [ p_name spine_idx ] )
                                  in
                                  let subst_motive =
                                    Surface.Lambda
                                      { name = Named "__v"
                                      ; bound =
                                          Surface.apply
                                            (Surface.Var [ ind_head ])
                                            [ Surface.Var [ "__v" ] ]
                                      ; implicit = false
                                      }
                                  in
                                  let coerced =
                                    Surface.apply
                                      (Surface.Var [ "subst" ])
                                      [ subst_motive
                                      ; Surface.Var [ dep_user_name ]
                                      ; value_surface
                                      ; cong_proof
                                      ; Surface.Var [ bind_user_name ]
                                      ]
                                  in
                                  let refined_ty =
                                    Surface.apply
                                      (Surface.Var [ ind_head ])
                                      [ value_surface ]
                                  in
                                  Some (bind_user_name, coerced, refined_ty))))))
                 (List.mapi (fun i k -> i, k) ctor_info_.binder_kinds))
             else []
           in
           let body =
             match sub_head.Surface.body with
             | Surface.Inline_elim d ->
               let coerce_for_target =
                 List.find_opt (fun (b, _, _) -> String.equal b d.target) coerce_wraps
               in
               let next_target_override =
                 match coerce_for_target with
                 | Some (_, expr, _) -> Some expr
                 | None -> None
               in
               let next_outer_subst =
                 if Option.is_some next_target_override then [] else sigma @ outer_subst
               in
               Surface.Inline_elim
                 { d with
                   siblings = new_siblings_for_next
                 ; outer_subst = next_outer_subst
                 ; target_override = next_target_override
                 }
             | other ->
               let body = subst_vars_surface sigma_renamings other in
               List.fold_left
                 (fun acc (bind_name, coerced_expr, refined_ty) ->
                    if not (occurs_in bind_name acc)
                    then acc
                    else
                      Surface.App
                        ( false
                        , Surface.TypedLambda
                            ( { Syntax.name = Syntax.Named bind_name
                              ; bound = refined_ty
                              ; implicit = false
                              }
                            , acc )
                        , coerced_expr ))
                 body
                 coerce_wraps
           in
           close_ctor_lambdas ~check_loc:loc vs (wrap_p_binders body)
         | Index_unify.Stuck _ -> assert false (* handled above *))
      ctor_outcomes
  in
  let target_full_spine_raw =
    match Evaluation.force_head target_type_raw with
    | Core.IndType (_, sp) -> Bwd.to_list sp
    | _ -> target_full_spine
  in
  let target_full_spine_surface = List.map readback_v target_full_spine_raw in
  let elim_param_imps =
    let pi = List.map (fun (p : _ Syntax.binder) -> p.implicit) info.params in
    let di = List.map (fun (d : _ Syntax.binder) -> d.implicit) info.deps in
    pi @ di
  in
  let refl_args =
    if id_reify then List.init m_indices (fun _ -> Surface.Var [ "Id"; "refl" ]) else []
  in
  let target_arg =
    match target_override with
    | Some e -> e
    | None -> Surface.Var [ target_name ]
  in
  let all_args =
    target_full_spine_surface @ [ target_arg; motive ] @ case_args @ refl_args
  in
  let n_spine = List.length target_full_spine_surface in
  List.fold_left
    (fun (acc, i) a ->
       let imp =
         i < n_spine && i < List.length elim_param_imps && List.nth elim_param_imps i
       in
       Surface.App (imp, acc, a), i + 1)
    (Surface.Var [ ind_head; "elim" ], 0)
    all_args
  |> fst
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

let%expect_test "rewrite_recursive_calls: case-suc of add" =
  (* Body: `add' m n` with `m` being a recursive case-arg. *)
  let body =
    Surface.App
      ( false
      , Surface.App (false, Surface.Var [ "add'" ], Surface.Var [ "m" ])
      , Surface.Var [ "n" ] )
  in
  let rewritten =
    rewrite_recursive_calls
      ~loc:(Asai.Range.of_lex_range (Lexing.dummy_pos, Lexing.dummy_pos))
      ~func_name:"add'"
      ~arity:2
      ~target_pos:0
      ~rec_arg_to_ih:[ "m", "add' m" ]
      body
  in
  print_string @@ [%show: Surface.preterm] rewritten;
  [%expect {| (add' m n) |}]
;;

let%expect_test "rewrite_recursive_calls: non-recursive call left alone" =
  let body =
    Surface.App
      ( false
      , Surface.App (false, Surface.Var [ "foo" ], Surface.Var [ "m" ])
      , Surface.Var [ "n" ] )
  in
  let rewritten =
    rewrite_recursive_calls
      ~loc:(Asai.Range.of_lex_range (Lexing.dummy_pos, Lexing.dummy_pos))
      ~func_name:"add'"
      ~arity:2
      ~target_pos:0
      ~rec_arg_to_ih:[ "m", "add' m" ]
      body
  in
  print_string @@ [%show: Surface.preterm] rewritten;
  [%expect {| ((foo m) n) |}]
;;

let%expect_test "compute_effective_intros: bracketed intro at explicit param errors" =
  let result =
    try
      with_handlers (fun () ->
        let dummy_loc = Asai.Range.of_lex_range (Lexing.dummy_pos, Lexing.dummy_pos) in
        let _ =
          compute_effective_intros
            ~loc:dummy_loc
            ~bindings:
              [ ({ name = Named "A"; bound = Surface.Universe; implicit = false }
                 : Surface.pretype binder)
              ]
            ~signature:Surface.Universe
            ~intros:[ "A", true ]
        in
        ());
      "no error raised"
    with
    | Failure msg -> "raised: " ^ msg
  in
  Printf.printf "%s" result;
  [%expect {| raised: Reporter.Message.Elab_error |}]
;;
