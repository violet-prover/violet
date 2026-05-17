module Syntax = Violet_kernel.Syntax
module ElabData = Driver
open Syntax
open Asai.Range
open Surface_utils

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

(* Rename free Var occurrences in a Surface preterm. Respects binders: when
   we descend under a Lambda/TypedLambda/Pi whose name shadows a key in the
   renaming, that key is dropped for the inner scope. *)
let rec rename_vars_surface (renaming : (string * string) list) (t : Surface.preterm)
  : Surface.preterm
  =
  if renaming = []
  then t
  else (
    match t with
    | Surface.Located { value; loc } ->
      Surface.Located { value = rename_vars_surface renaming value; loc }
    | Surface.Var [ n ] ->
      (match List.assoc_opt n renaming with
       | Some n' -> Surface.Var [ n' ]
       | None -> t)
    | Surface.Var _ -> t (* multi-segment names aren't subject to local renaming *)
    | Surface.App (impl, f, a) ->
      Surface.App (impl, rename_vars_surface renaming f, rename_vars_surface renaming a)
    | Surface.Lambda b ->
      let renaming' = List.filter (fun (k, _) -> not (String.equal k b.name)) renaming in
      Surface.Lambda { b with bound = rename_vars_surface renaming' b.bound }
    | Surface.TypedLambda (b, body) ->
      let bound' = rename_vars_surface renaming b.bound in
      let renaming' = List.filter (fun (k, _) -> not (String.equal k b.name)) renaming in
      Surface.TypedLambda ({ b with bound = bound' }, rename_vars_surface renaming' body)
    | Surface.Pi (b, body) ->
      let bound' = rename_vars_surface renaming b.bound in
      let renaming' = List.filter (fun (k, _) -> not (String.equal k b.name)) renaming in
      Surface.Pi ({ b with bound = bound' }, rename_vars_surface renaming' body)
    | Surface.Max (a, b) ->
      Surface.Max (rename_vars_surface renaming a, rename_vars_surface renaming b)
    | Surface.Universe | Surface.Hole | Surface.Goal _ -> t
    | Surface.Op_soup _ ->
      Reporter.fatalf
        Elab_error
        "internal: Op_soup reached rename_vars_surface (resolver should have lowered it)"
    | Surface.RecordLit entries ->
      Surface.RecordLit
        (List.map (fun (f, e) -> f, rename_vars_surface renaming e) entries)
    | Surface.RecordUpdate (base, entries) ->
      Surface.RecordUpdate
        ( rename_vars_surface renaming base
        , List.map (fun (f, e) -> f, rename_vars_surface renaming e) entries )
    | Surface.Proj (e, f) -> Surface.Proj (rename_vars_surface renaming e, f))
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
  let rec walk shadowed t =
    match t with
    | Surface.Located { value; loc } ->
      Surface.Located { value = walk shadowed value; loc }
    | Surface.Var [ n ] when is_ctor n && not (List.mem n shadowed) ->
      Surface.Var [ ind_head; n ]
    | Surface.Var _ -> t
    | Surface.App (impl, f, a) -> Surface.App (impl, walk shadowed f, walk shadowed a)
    | Surface.Lambda b ->
      Surface.Lambda { b with bound = walk (b.name :: shadowed) b.bound }
    | Surface.TypedLambda (b, body) ->
      let bound' = walk shadowed b.bound in
      Surface.TypedLambda ({ b with bound = bound' }, walk (b.name :: shadowed) body)
    | Surface.Pi (b, body) ->
      let bound' = walk shadowed b.bound in
      Surface.Pi ({ b with bound = bound' }, walk (b.name :: shadowed) body)
    | Surface.Max (a, b) -> Surface.Max (walk shadowed a, walk shadowed b)
    | Surface.Universe | Surface.Hole | Surface.Goal _ -> t
    | Surface.Op_soup _ ->
      Reporter.fatalf
        Elab_error
        "internal: Op_soup reached qualify_ctor_names (resolver should have lowered it)"
    | Surface.RecordLit entries ->
      Surface.RecordLit (List.map (fun (f, e) -> f, walk shadowed e) entries)
    | Surface.RecordUpdate (base, entries) ->
      Surface.RecordUpdate
        (walk shadowed base, List.map (fun (f, e) -> f, walk shadowed e) entries)
    | Surface.Proj (e, f) -> Surface.Proj (walk shadowed e, f)
  in
  walk shadowed body
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
    | Surface.Op_soup _ ->
      Reporter.fatalf
        Elab_error
        "internal: Op_soup reached clause-body rewrite (resolver should have lowered it)"
    | Surface.RecordLit entries ->
      Surface.RecordLit (List.map (fun (f, e) -> f, rw e) entries)
    | Surface.RecordUpdate (base, entries) ->
      Surface.RecordUpdate (rw base, List.map (fun (f, e) -> f, rw e) entries)
    | Surface.Proj (e, f) -> Surface.Proj (rw e, f)
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
  let rec walk_pi params sig_rem user =
    match params, user with
    | (_, true) :: prest, (uname, true) :: urest ->
      (uname, true) :: walk_pi prest sig_rem urest
    | (pname, true) :: prest, _ -> (pname, true) :: walk_pi prest sig_rem user
    | (_, false) :: prest, (uname, false) :: urest ->
      (uname, false) :: walk_pi prest sig_rem urest
    | (pname, false) :: _, (uname, true) :: _ ->
      Reporter.fatalf
        ~loc
        Elab_error
        "intro `{%s}` provided at explicit param `%s`"
        uname
        pname
    | (pname, false) :: _, [] ->
      Reporter.fatalf ~loc Elab_error "missing intro for explicit param `%s`" pname
    | [], _ -> walk_sig sig_rem user
  and walk_sig s user =
    match s, user with
    | _, [] -> []
    | Surface.Located { value; _ }, _ -> walk_sig value user
    | Surface.Pi (b, cod), (uname, true) :: urest when b.implicit ->
      (uname, true) :: walk_sig cod urest
    | Surface.Pi (b, cod), _ when b.implicit -> (b.name, true) :: walk_sig cod user
    | Surface.Pi (b, cod), (uname, false) :: urest when not b.implicit ->
      (uname, false) :: walk_sig cod urest
    | Surface.Pi (b, _), (uname, true) :: _ ->
      Reporter.fatalf
        ~loc
        Elab_error
        "intro `{%s}` at explicit Pi-binder `%s`"
        uname
        b.name
    | _, (uname, _) :: _ ->
      Reporter.fatalf ~loc Elab_error "intro `%s` has no matching Pi-layer" uname
  in
  let param_binders =
    List.map (fun (b : Surface.pretype binder) -> b.name, b.implicit) bindings
  in
  walk_pi param_binders signature intros
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
      ~(opens : string list)
      ~(intros : (string * bool) list)
      ~(target : string)
      ~(clauses : Surface.clause list)
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
      | Surface.Var [ n ] -> n
      | Surface.Var _ ->
        Reporter.fatalf
          ~loc:(Option.value (loc_of target_type_surface) ~default:loc)
          Elab_error
          "elim: target's type head must be a bare inductive name"
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
  let dep_renaming : (string * string) list =
    List.mapi
      (fun i a ->
         match strip_loc a with
         | Surface.Var [ n ] -> n, Printf.sprintf "__elim_idx_%d" i
         | Surface.Var _ ->
           Reporter.fatalf
             ~loc
             Elab_error
             "elim: qualified path in index position is not yet supported"
         | _ ->
           Reporter.fatalf
             ~loc
             Elab_error
             "elim: non-variable index in target type `%s` is not yet supported"
             ind_head)
      dep_args
  in
  let motive : Surface.preterm =
    let body0 = peel_pi_surface ~loc (target_pos - np + 1) signature in
    let body = rename_vars_surface dep_renaming body0 in
    let inner = Surface.Lambda { name = target; bound = body; implicit = false } in
    List.fold_right
      (fun (_, fresh) acc ->
         Surface.Lambda { name = fresh; bound = acc; implicit = false })
      dep_renaming
      inner
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
                  let aligned =
                    align_clause_patterns
                      ~loc:(Option.value (loc_of c.body) ~default:loc)
                      intros
                      c.patterns
                  in
                  match Option.map normalize (List.nth_opt aligned target_pos) with
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
         let aligned_patterns =
           align_clause_patterns
             ~loc:(Option.value (loc_of clause.body) ~default:loc)
             intros
             clause.patterns
         in
         if not (String.equal clause.head func_name)
         then
           Reporter.fatalf
             ~loc:clause_loc
             Elab_error
             "elim clause head `%s` does not match function name `%s`"
             clause.head
             func_name;
         let vs =
           match Option.map normalize (List.nth_opt aligned_patterns target_pos) with
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
           List.filteri (fun i _ -> i > target_pos) aligned_patterns
           |> List.map (function
             | Surface.PVar n -> n
             | Surface.PCon _ ->
               Reporter.fatalf
                 ~loc:clause_loc
                 Elab_error
                 "elim: pattern at non-target position must be a variable"
             | Surface.PImpVar _ ->
               assert false (* normalized away by align_clause_patterns *)
             | Surface.PRecord _ ->
               Reporter.fatalf
                 ~loc:clause_loc
                 Elab_error
                 "elim: record pattern at non-target position must be a variable")
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
         let qualified_body =
           let ih_names = List.map snd rec_arg_to_ih in
           let param_names =
             List.map (fun (b : Surface.pretype binder) -> b.name) params
           in
           let intro_names = List.map fst intros in
           let shadowed =
             vs @ ih_names @ trailing_pattern_names @ intro_names @ param_names
           in
           let opened_namespaces =
             (* Scrutinee's namespace is auto-opened; then user-listed `open`s. *)
             (ind_head, List.map fst ctors)
             :: List.map
                  (fun open_name ->
                     let opened_info : ElabData.ind_info =
                       match Context.S.resolve [ open_name ] with
                       | Some (_, `Inductive i) -> i
                       | _ ->
                         Reporter.fatalf
                           ~loc:clause_loc
                           Elab_error
                           "`open %s`: not an inductive"
                           open_name
                     in
                     open_name, List.map fst (ElabData.arities_of opened_info))
                  opens
           in
           List.fold_left
             (fun body (head, ctor_names) ->
                qualify_ctor_names ~ind_head:head ~ctor_names ~shadowed body)
             rewritten_body
             opened_namespaces
         in
         let with_trailing =
           List.fold_right
             (fun n body -> Surface.Lambda { name = n; bound = body; implicit = false })
             trailing_pattern_names
             qualified_body
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
      (Surface.Var [ ind_head; "elim" ])
      (data_args @ [ Surface.Var [ target ]; motive ] @ case_args)
  in
  List.fold_left
    (fun acc (n, _) -> Surface.App (false, acc, Surface.Var [ n ]))
    elim_call
    trailing_intros
;;

(* Internal: run a thunk under all elaboration effect handlers. Used by
   inline tests below. *)
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
      ~rec_arg_to_ih:[ "m", "ih-m" ]
      body
  in
  print_string @@ [%show: Surface.preterm] rewritten;
  [%expect {| (ih-m n) |}]
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
      ~rec_arg_to_ih:[ "m", "ih-m" ]
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
              [ ({ name = "A"; bound = Surface.Universe; implicit = false }
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
