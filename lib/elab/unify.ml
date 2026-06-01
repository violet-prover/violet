open Violet_common
module Syntax = Violet_kernel.Syntax
module Evaluation = Wiring.Eval
module Level = Violet_kernel.Level
module Context_view = Violet_kernel.Context_view
module Pretty = Violet_kernel.Pretty
open Syntax
open Bwd
open Evaluation

module PartialRenaming = struct
  open Core

  (* Raised when renaming hits a local that is not among the meta's arguments.
     Carries the offending de Bruijn LEVEL plus the context at the point of the
     escape, so the caller can render the variable by its surface name. Caught
     locally during pruning; otherwise surfaced as an Elab_error in `run`. *)
  exception Escaping of int * Context_view.t

  (* dom = size of the meta's argument context (LHS, fresh after invert)
     cod = size of the surrounding context the meta lives in (RHS)
     ren = cod-level → dom-level (where each spine element ended up) *)
  type t =
    { dom : int
    ; cod : int
    ; ren : (int, int) Hashtbl.t
    }

  let invert (cv : Context_view.t) (sp : value bwd) : t =
    let ren = Hashtbl.create ~random:true 16 in
    (* Iterate the spine LEFT-TO-RIGHT (outermost arg first) so the dom-side
       position we assign matches argument-order in the solution.  Bwd.iter
       is right-to-left, so go via to_list / List.iteri here. *)
    let sp_list = Bwd.to_list sp in
    List.iteri
      (fun pos v ->
         match force v with
         | RigidLocal (l, Emp) ->
           if Hashtbl.mem ren l
           then Reporter.fatalf Elab_error "non-linear spine (level $%d repeated)" l
           else Hashtbl.add ren l pos
         | other ->
           Reporter.fatalf
             Elab_error
             "non-variable in spine: %s"
             (Pretty.pp_term cv (Evaluation.quote (Context_view.lvl cv) other)))
      sp_list;
    { dom = List.length sp_list; cod = Context_view.lvl cv; ren }
  ;;

  (* Wrap a term in `dom` outer Lambdas so the solution can stand alone.
     Names are placeholders for pretty printing only. *)
  let lams (dom : int) (tm : term) : term =
    let rec go i acc =
      if i = dom
      then acc
      else
        go
          (i + 1)
          (Lambda
             { name = Named (Printf.sprintf "x%d" (dom - i - 1))
             ; implicit = false
             ; bound = acc
             })
    in
    go 0 tm
  ;;

  let rec rename (m : metavar) (cv : Context_view.t) (pr : t) (v : value) : term =
    match force v with
    | Universe l -> Universe l
    | Flex (m', _) when m = m' ->
      Reporter.fatalf
        Elab_error
        "meta variable %s occurs in its own solution"
        (Pretty.pp_metavar m)
    | Flex (m', sp) -> rename_flex m cv pr m' sp
    | RigidLocal (l, sp) ->
      (match Hashtbl.find_opt pr.ren l with
       | None -> raise (Escaping (l, cv))
       | Some l' ->
         (* l' is a dom-level; convert to term-side de Bruijn INDEX *)
         rename_sp m cv pr (LocalVar (pr.dom - l' - 1)) sp)
    | Var (x, sp) -> rename_sp m cv pr (Var x) sp
    | Label (x, sp) -> rename_sp m cv pr (Var x) sp
    | IndType (x, sp) -> rename_sp m cv pr (Var x) sp
    | Elim ({ elim_name; _ }, sp) -> rename_sp m cv pr (Var elim_name) sp
    | VLambda { name; bound = clos; implicit } ->
      let cv' = Context_view.extend cv (Syntax.Name.to_string name) in
      Hashtbl.add pr.ren pr.cod pr.dom;
      let body =
        rename
          m
          cv'
          { pr with cod = pr.cod + 1; dom = pr.dom + 1 }
          (clos (RigidLocal (pr.cod, Emp)))
      in
      Hashtbl.remove pr.ren pr.cod;
      Lambda { name; implicit; bound = body }
    | VPi ({ name; bound = a; implicit }, b) ->
      let a' = rename m cv pr a in
      let cv' = Context_view.extend cv (Syntax.Name.to_string name) in
      Hashtbl.add pr.ren pr.cod pr.dom;
      let b' =
        rename
          m
          cv'
          { pr with cod = pr.cod + 1; dom = pr.dom + 1 }
          (b (RigidLocal (pr.cod, Emp)))
      in
      Hashtbl.remove pr.ren pr.cod;
      Pi ({ name; bound = a'; implicit }, b')
    | VLift { from_lvl; to_lvl; ty } -> Lift { from_lvl; to_lvl; ty = rename m cv pr ty }
    | VLiftTerm { from_lvl; to_lvl; ty; tm } ->
      LiftTerm { from_lvl; to_lvl; ty = rename m cv pr ty; tm = rename m cv pr tm }
    | VUnliftTerm { from_lvl; to_lvl; ty; tm } ->
      UnliftTerm { from_lvl; to_lvl; ty = rename m cv pr ty; tm = rename m cv pr tm }
    | VRecordType { name; params; fields; field_env = _; field_terms = _ } ->
      let t_params = List.map (rename m cv pr) params in
      let rec walk cv pr = function
        | [] -> []
        | (b : value Syntax.binder) :: rest ->
          let t_bound = rename m cv pr b.bound in
          let cv' = Context_view.extend cv (Syntax.Name.to_string b.name) in
          Hashtbl.add pr.ren pr.cod pr.dom;
          let pr' = { pr with cod = pr.cod + 1; dom = pr.dom + 1 } in
          let t_rest = walk cv' pr' rest in
          Hashtbl.remove pr.ren pr.cod;
          { Syntax.name = b.name; bound = t_bound; implicit = b.implicit } :: t_rest
      in
      RecordType { name; params = t_params; fields = walk cv pr fields }
    | VRecordIntro { name; fields } ->
      RecordIntro { name; fields = List.map (fun (f, v) -> f, rename m cv pr v) fields }
    | VRecordProj (v, f, sp) ->
      rename_sp m cv pr (RecordProj { record = rename m cv pr v; field = f }) sp
    | VIdAbsurd v -> IdAbsurd (rename m cv pr v)
    | VEmpty -> Empty
    | VAbsurd (s, sp) -> rename_sp m cv pr (Absurd (rename m cv pr s)) sp

  and rename_sp (m : metavar) (cv : Context_view.t) (pr : t) (t : term) (sp : value bwd)
    : term
    =
    match sp with
    | Emp -> t
    | Snoc (sp, u) -> App (rename_sp m cv pr t sp, rename m cv pr u)

  (* Rename an occurrence `m' sp` appearing in the solution of `m`.

     If every argument renames, this is just `rename_sp` over `Meta m'`.
     Otherwise some argument references a local outside `m`'s spine — but it
     does so only as an ARGUMENT to the flex meta `m'`, so we PRUNE those
     positions: mint a fresh `m''` and solve

         m' := λ x0 … x_{k-1}. m'' (x_j for each surviving position j)

     then refer to `m''` here, applied to just the surviving (renamed) args.
     `m''` may stay unsolved; if a pruned position was actually needed, the
     kernel's re-check of the final solution rejects it (no unsoundness). *)
  and rename_flex
        (m : metavar)
        (cv : Context_view.t)
        (pr : t)
        (m' : metavar)
        (sp : value bwd)
    : term
    =
    let args = Bwd.to_list sp in
    let k = List.length args in
    let classified =
      List.map
        (fun u ->
           match rename m cv pr u with
           | t -> `Keep t
           | exception Escaping _ -> `Drop)
        args
    in
    if List.for_all (function `Keep _ -> true | `Drop -> false) classified
    then
      List.fold_left
        (fun acc -> function
           | `Keep t -> App (acc, t)
           | `Drop -> assert false (* unreachable: all are Keep here *))
        (Meta m')
        classified
    else begin
      let m'' = Meta.fresh_metavar () in
      (* Build m''s arguments inside the k binders of m's new solution.
         Spine position j is bound to de Bruijn INDEX k-1-j. *)
      let m'_body, _ =
        List.fold_left
          (fun (acc, j) cl ->
             match cl with
             | `Keep _ -> App (acc, LocalVar (k - 1 - j)), j + 1
             | `Drop -> acc, j + 1)
          (Meta m'', 0)
          classified
      in
      Meta.insert_meta m' (eval Emp (lams k m'_body));
      List.fold_left
        (fun acc -> function
           | `Keep t -> App (acc, t)
           | `Drop -> acc)
        (Meta m'')
        classified
    end
  ;;

  let run (cv : Context_view.t) (m : metavar) (sp : value bwd) (rhs : value) : value =
    let pr = invert cv sp in
    let rhs_tm =
      try rename m cv pr rhs with
      | Escaping (l, cv') ->
        Reporter.fatalf
          Elab_error
          "local `%s` escapes the solution of %s: it is not one of the meta's \
           arguments, so the solution may not mention it"
          (Pretty.pp_term cv' (Evaluation.quote (Context_view.lvl cv') (RigidLocal (l, Emp))))
          (Pretty.pp_metavar m)
    in
    let solution = lams pr.dom rhs_tm in
    Reporter.tracef "solution is: %s" (Pretty.pp_term Context_view.empty solution)
    @@ fun () -> eval Emp solution
  ;;
end

let solve
      (cv : Context_view.t)
      (m : Core.metavar)
      (sp : Core.value bwd)
      (rhs : Core.value)
  : unit
  =
  let spine_str =
    String.concat " <: "
    @@ List.map
         (fun v -> Pretty.pp_term cv (Evaluation.quote (Context_view.lvl cv) v))
         (Bwd.to_list sp)
  in
  Reporter.tracef "spine: %s" spine_str
  @@ fun () ->
  let solution = PartialRenaming.run cv m sp rhs in
  Meta.insert_meta m solution
;;

let unify_level ~loc (l1 : Level.level) (l2 : Level.level) : unit =
  if Level.equal l1 l2
  then ()
  else (
    let has_foreign =
      let check_atom (a : Level.atom) = not (Context.is_level_var a.var) in
      let n1 = Level.normalize l1 in
      let n2 = Level.normalize l2 in
      List.exists check_atom n1.atoms || List.exists check_atom n2.atoms
    in
    if has_foreign
    then ()
    else
      Reporter.fatalf
        ~loc
        Type_error
        "cannot unify `universe %s ?= universe %s`"
        (Level.pretty l1)
        (Level.pretty l2))
;;

let rec unify ~loc (cv : Context_view.t) (a : Core.value) (b : Core.value) : unit =
  Reporter.tracef
    ~loc
    "unify `%s` and `%s`"
    (Pretty.pp_term cv (Evaluation.quote (Context_view.lvl cv) a))
    (Pretty.pp_term cv (Evaluation.quote (Context_view.lvl cv) b))
  @@ fun () ->
  (* force_head unfolds metas AND opaque global heads.  After this, the only
     way to still see a Var(x, sp) head is if `x` has no definition (axiom). *)
  match force_head a, force_head b with
  | Universe l1, Universe l2 -> unify_level ~loc l1 l2
  | VLift a, VLift b ->
    unify_level ~loc a.from_lvl b.from_lvl;
    unify_level ~loc a.to_lvl b.to_lvl;
    unify ~loc cv a.ty b.ty
  | VLiftTerm a, VLiftTerm b ->
    unify_level ~loc a.from_lvl b.from_lvl;
    unify_level ~loc a.to_lvl b.to_lvl;
    unify ~loc cv a.ty b.ty;
    unify ~loc cv a.tm b.tm
  | VUnliftTerm a, VUnliftTerm b ->
    unify_level ~loc a.from_lvl b.from_lvl;
    unify_level ~loc a.to_lvl b.to_lvl;
    unify ~loc cv a.ty b.ty;
    unify ~loc cv a.tm b.tm
  | RigidLocal (l1, sp1), RigidLocal (l2, sp2) when l1 = l2 -> unify_spine ~loc cv sp1 sp2
  | Var (h1, sp1), Var (h2, sp2) when String.equal h1 h2 -> unify_spine ~loc cv sp1 sp2
  | Label (h1, sp1), Label (h2, sp2) when String.equal h1 h2 ->
    unify_spine ~loc cv sp1 sp2
  | IndType (h1, sp1), IndType (h2, sp2) when String.equal h1 h2 ->
    unify_spine ~loc cv sp1 sp2
  | Elim (h1, sp1), Elim (h2, sp2) when String.equal h1.elim_name h2.elim_name ->
    unify_spine ~loc cv sp1 sp2
  | VRecordProj (v1, f1, sp1), VRecordProj (v2, f2, sp2) when String.equal f1 f2 ->
    unify ~loc cv v1 v2;
    unify_spine ~loc cv sp1 sp2
  | VIdAbsurd v1, VIdAbsurd v2 -> unify ~loc cv v1 v2
  | VEmpty, VEmpty -> ()
  | VAbsurd (s1, sp1), VAbsurd (s2, sp2) ->
    unify ~loc cv s1 s2;
    unify_spine ~loc cv sp1 sp2
  | VLambda { name; bound = b1; _ }, VLambda { bound = b2; _ } ->
    let x = Core.RigidLocal (Context_view.lvl cv, Emp) in
    unify ~loc (Context_view.extend cv (Syntax.Name.to_string name)) (b1 x) (b2 x)
  | VLambda { name; bound; _ }, t | t, VLambda { name; bound; _ } ->
    let x = Core.RigidLocal (Context_view.lvl cv, Emp) in
    unify ~loc (Context_view.extend cv (Syntax.Name.to_string name)) (bound x) (vapp t x)
  (* Record types are equal if they have the same name and equal parameters. *)
  | VRecordType r1, VRecordType r2 when String.equal r1.name r2.name ->
    List.iter2 (unify ~loc cv) r1.params r2.params
  (* Record η. Standard surjective-pairing: a value of record type is
     definitionally equal to the record literal of its projections. *)
  | VRecordIntro r1, VRecordIntro r2 when r1.name = r2.name ->
    if List.length r1.fields <> List.length r2.fields
    then
      Reporter.fatalf
        ~loc
        Type_error
        "record %s: field count mismatch (%d vs %d)"
        r1.name
        (List.length r1.fields)
        (List.length r2.fields);
    (* Field sets must agree (modulo ordering); unify each by name. *)
    List.iter
      (fun (f, v1) ->
         match List.assoc_opt f r2.fields with
         | Some v2 -> unify ~loc cv v1 v2
         | None ->
           Reporter.fatalf
             ~loc
             Type_error
             "record %s: field `%s` not in both intros"
             r1.name
             f)
      r1.fields
  | VRecordIntro r, Flex (m, sp) | Flex (m, sp), VRecordIntro r ->
    (* One side is a flex meta; solve it directly with the whole record literal.
       Projecting fields from a flex produces stuck neutrals that the unifier
       cannot resolve, so we short-circuit by solving m := VRecordIntro r. *)
    solve cv m sp (VRecordIntro r)
  | VRecordIntro r, t | t, VRecordIntro r ->
    (* One side is a record literal; eta-expand the other by projecting each
       field. The expanded sides are then compared field-by-field. *)
    List.iter
      (fun (f, v_lit) ->
         let v_proj = vrecord_proj t f in
         unify ~loc cv v_lit v_proj)
      r.fields
  | VPi ({ name; _ }, b1), VPi (_, b2) ->
    let x = Core.RigidLocal (Context_view.lvl cv, Emp) in
    unify ~loc (Context_view.extend cv (Syntax.Name.to_string name)) (b1 x) (b2 x)
  | VPi ({ implicit = true; name = pi_name; bound = a }, b), t
  | t, VPi ({ implicit = true; name = pi_name; bound = a }, b) ->
    let display =
      Printf.sprintf
        "{%s : %s}"
        (Syntax.Name.to_string pi_name)
        (Pretty.pp_term cv (Evaluation.quote (Context_view.lvl cv) a))
    in
    let x = Meta.fresh_meta_value_with (Context_view.lvl cv) ~origin:{ loc; display } in
    unify ~loc cv (b x) t
  | Flex (m1, sp1), Flex (m2, sp2) when m1 = m2 -> unify_spine ~loc cv sp1 sp2
  | t, Flex (m, sp) | Flex (m, sp), t -> solve cv m sp t
  | expected, actual ->
    Reporter.fatalf
      ~loc
      Type_error
      "cannot unify `%s ?= %s` (or verbose `%s ?= %s`)"
      (Pretty.pp_term cv (Evaluation.quote (Context_view.lvl cv) expected))
      (Pretty.pp_term cv (Evaluation.quote (Context_view.lvl cv) actual))
      (Pretty.pp_term cv (Evaluation.quote (Context_view.lvl cv) a))
      (Pretty.pp_term cv (Evaluation.quote (Context_view.lvl cv) b))

and unify_spine ~loc (cv : Context_view.t) (xs : Core.value bwd) (ys : Core.value bwd)
  : unit
  =
  match xs, ys with
  | Emp, Emp -> ()
  | Snoc (xs, x), Snoc (ys, y) ->
    unify_spine ~loc cv xs ys;
    unify ~loc cv x y
  | _, _ ->
    let left =
      String.concat " <: "
      @@ Bwd.to_list
      @@ Bwd.map
           (fun x -> Pretty.pp_term cv (Evaluation.quote (Context_view.lvl cv) x))
           xs
    in
    let right =
      String.concat " <: "
      @@ Bwd.to_list
      @@ Bwd.map
           (fun y -> Pretty.pp_term cv (Evaluation.quote (Context_view.lvl cv) y))
           ys
    in
    Reporter.fatalf
      ~loc
      Elab_error
      "cannot unify spine `%s` and `%s`, spine mismatched"
      left
      right
;;

let%expect_test "record eta: VRecordIntro vs neutral unifies" =
  (* If `t = RigidLocal 0` and lit = { x = t.x, y = t.y }, then
     unify should succeed: the literal is definitionally equal to t. *)
  let t : Core.value = Core.RigidLocal (0, Emp) in
  let lit : Core.value =
    Core.VRecordIntro
      { name = "Point"
      ; fields =
          [ "x", Core.VRecordProj (t, "x", Emp); "y", Core.VRecordProj (t, "y", Emp) ]
      }
  in
  let result =
    Reporter.run ~emit:(fun _ -> ()) ~fatal:(fun _ -> "FAILED")
    @@ fun () ->
    unify
      ~loc:(Asai.Range.of_lex_range (Lexing.dummy_pos, Lexing.dummy_pos))
      (Context_view.make ~names:(Snoc (Emp, "_")) ~lvl:1)
      t
      lit;
    "ok"
  in
  print_endline result;
  [%expect {| ok |}]
;;

let%expect_test "lambda eta: (fun x => f x) unifies with f" =
  let loc = Asai.Range.of_lex_range (Lexing.dummy_pos, Lexing.dummy_pos) in
  let cv = Context_view.make ~names:(Snoc (Emp, "f")) ~lvl:1 in
  let f : Core.value = Core.RigidLocal (0, Emp) in
  let eta_f : Core.value =
    Core.VLambda
      { name = Named "x"
      ; implicit = false
      ; bound = (fun x -> Core.RigidLocal (0, Snoc (Emp, x)))
      }
  in
  let result =
    Reporter.run ~emit:(fun _ -> ()) ~fatal:(fun _ -> "FAILED")
    @@ fun () ->
    unify ~loc cv f eta_f;
    "ok"
  in
  print_endline result;
  [%expect {| ok |}]
;;

let%expect_test "Pi codomain mismatch rejects" =
  let loc = Asai.Range.of_lex_range (Lexing.dummy_pos, Lexing.dummy_pos) in
  let cv = Context_view.empty in
  let pi1 =
    Core.VPi
      ( { name = Named "x"; bound = Core.Universe Level.LZero; implicit = false }
      , fun _ -> Core.Universe Level.LZero )
  in
  let pi2 =
    Core.VPi
      ( { name = Named "x"; bound = Core.Universe Level.LZero; implicit = false }
      , fun _ -> Core.Universe (Level.lsuc Level.LZero) )
  in
  let result =
    Reporter.run ~emit:(fun _ -> ()) ~fatal:(fun _ -> "FAILED")
    @@ fun () ->
    unify ~loc cv pi1 pi2;
    "ok"
  in
  print_endline result;
  [%expect {| FAILED |}]
;;

let%expect_test "spine mismatch rejects cleanly" =
  let loc = Asai.Range.of_lex_range (Lexing.dummy_pos, Lexing.dummy_pos) in
  let cv = Context_view.make ~names:(Snoc (Snoc (Emp, "a"), "b")) ~lvl:2 in
  let v1 : Core.value = Core.RigidLocal (0, Snoc (Emp, Core.Universe Level.LZero)) in
  let v2 : Core.value =
    Core.RigidLocal (0, Snoc (Emp, Core.Universe (Level.lsuc Level.LZero)))
  in
  let result =
    Reporter.run ~emit:(fun _ -> ()) ~fatal:(fun _ -> "FAILED")
    @@ fun () ->
    unify ~loc cv v1 v2;
    "ok"
  in
  print_endline result;
  [%expect {| FAILED |}]
;;

let%expect_test "same rigid head with same spine unifies" =
  let loc = Asai.Range.of_lex_range (Lexing.dummy_pos, Lexing.dummy_pos) in
  let cv = Context_view.make ~names:(Snoc (Snoc (Emp, "f"), "a")) ~lvl:2 in
  let arg : Core.value = Core.RigidLocal (1, Emp) in
  let v : Core.value = Core.RigidLocal (0, Snoc (Emp, arg)) in
  let result =
    Reporter.run ~emit:(fun _ -> ()) ~fatal:(fun _ -> "FAILED")
    @@ fun () ->
    unify ~loc cv v v;
    "ok"
  in
  print_endline result;
  [%expect {| ok |}]
;;

let%expect_test "distinct rigid heads reject" =
  let loc = Asai.Range.of_lex_range (Lexing.dummy_pos, Lexing.dummy_pos) in
  let cv = Context_view.make ~names:(Snoc (Snoc (Emp, "a"), "b")) ~lvl:2 in
  let v1 : Core.value = Core.RigidLocal (0, Emp) in
  let v2 : Core.value = Core.RigidLocal (1, Emp) in
  let result =
    Reporter.run ~emit:(fun _ -> ()) ~fatal:(fun _ -> "FAILED")
    @@ fun () ->
    unify ~loc cv v1 v2;
    "ok"
  in
  print_endline result;
  [%expect {| FAILED |}]
;;

let%expect_test "universe level mismatch rejects" =
  let loc = Asai.Range.of_lex_range (Lexing.dummy_pos, Lexing.dummy_pos) in
  let cv = Context_view.empty in
  let result =
    Reporter.run ~emit:(fun _ -> ()) ~fatal:(fun _ -> "FAILED")
    @@ fun () ->
    unify ~loc cv (Core.Universe Level.LZero) (Core.Universe (Level.lsuc Level.LZero));
    "ok"
  in
  print_endline result;
  [%expect {| FAILED |}]
;;

let%expect_test "universe same level unifies" =
  let loc = Asai.Range.of_lex_range (Lexing.dummy_pos, Lexing.dummy_pos) in
  let cv = Context_view.empty in
  let result =
    Reporter.run ~emit:(fun _ -> ()) ~fatal:(fun _ -> "FAILED")
    @@ fun () ->
    unify ~loc cv (Core.Universe Level.LZero) (Core.Universe Level.LZero);
    "ok"
  in
  print_endline result;
  [%expect {| ok |}]
;;

let%expect_test "meta solving: flex = rigid solves meta" =
  let loc = Asai.Range.of_lex_range (Lexing.dummy_pos, Lexing.dummy_pos) in
  let cv = Context_view.make ~names:(Snoc (Emp, "x")) ~lvl:1 in
  let m = Core.MetaVar 99999 in
  let x : Core.value = Core.RigidLocal (0, Emp) in
  let flex : Core.value = Core.Flex (m, Snoc (Emp, x)) in
  let target : Core.value = Core.Universe Level.LZero in
  let result =
    Reporter.run ~emit:(fun _ -> ()) ~fatal:(fun _ -> "FAILED")
    @@ fun () ->
    unify ~loc cv flex target;
    match Meta.lookup_meta m with
    | Some _ -> "solved"
    | None -> "unsolved"
  in
  print_endline result;
  [%expect {| solved |}]
;;

let%expect_test "pruning: escaping var that appears only under another flex meta is \
                 pruned, so the solve succeeds" =
  (* context: a (lvl 0), b (lvl 1) *)
  let cv = Context_view.make ~names:(Snoc (Snoc (Emp, "a"), "b")) ~lvl:2 in
  let m1 = Core.MetaVar 70001 in
  let m2 = Core.MetaVar 70002 in
  let a : Core.value = Core.RigidLocal (0, Emp) in
  let b : Core.value = Core.RigidLocal (1, Emp) in
  (* Solve `?m1 a := Stack (?m2 a b)`.  `b` is NOT in m1's spine, so it escapes
     — but it only occurs as an argument to the other flex meta `?m2`, exactly
     the case pruning resolves (drop `b` from m2). *)
  let rhs : Core.value =
    Core.Var ("Stack", Snoc (Emp, Core.Flex (m2, Snoc (Snoc (Emp, a), b))))
  in
  let result =
    Reporter.run ~emit:(fun _ -> ()) ~fatal:(fun _ -> "FAILED")
    @@ fun () ->
    solve cv m1 (Snoc (Emp, a)) rhs;
    match Meta.lookup_meta m1 with
    | Some _ -> "solved"
    | None -> "unsolved"
  in
  print_endline result;
  [%expect {| solved |}]
;;

let%expect_test "a genuine (un-prunable) escape names the offending variable \
                 instead of printing a raw de Bruijn level" =
  (* context: a (lvl 0), b (lvl 1).  Solve `?m a := b`: `b` escapes and there is
     no flex meta to prune it through, so this is a real error.  The message
     must name `b`, not `$1`. *)
  let cv = Context_view.make ~names:(Snoc (Snoc (Emp, "a"), "b")) ~lvl:2 in
  let m = Core.MetaVar 70003 in
  let a : Core.value = Core.RigidLocal (0, Emp) in
  let b : Core.value = Core.RigidLocal (1, Emp) in
  let result =
    Reporter.run
      ~emit:(fun _ -> ())
      ~fatal:(fun (d : Reporter.Message.t Asai.Diagnostic.t) ->
        Format.asprintf "%t" d.explanation.value)
    @@ fun () ->
    solve cv m (Snoc (Emp, a)) b;
    "NO ERROR"
  in
  print_endline result;
  [%expect
    {| local `b` escapes the solution of ?70003: it is not one of the meta's arguments, so the solution may not mention it |}]
;;

let%expect_test "quote renders a local by binder name in a unify context" =
  let cv = Context_view.empty in
  let cv = Context_view.extend cv "n" in
  let cv = Context_view.extend cv "x" in
  let v0 : Core.value = Core.RigidLocal (0, Emp) in
  let v1 : Core.value = Core.RigidLocal (1, Emp) in
  Printf.printf
    "%s, %s"
    (Pretty.pp_term cv (Evaluation.quote (Context_view.lvl cv) v0))
    (Pretty.pp_term cv (Evaluation.quote (Context_view.lvl cv) v1));
  [%expect {| n, x |}]
;;
