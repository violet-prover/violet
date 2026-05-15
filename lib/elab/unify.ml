module Syntax = Violet_kernel.Syntax
module Evaluation = Wiring.Eval
module Level = Violet_kernel.Level
open Syntax
open Bwd
open Evaluation

module PartialRenaming = struct
  open Core

  (* dom = size of the meta's argument context (LHS, fresh after invert)
     cod = size of the surrounding context the meta lives in (RHS)
     ren = cod-level → dom-level (where each spine element ended up) *)
  type t =
    { dom : int
    ; cod : int
    ; ren : (int, int) Hashtbl.t
    }

  let invert (gamma : int) (sp : value bwd) : t =
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
           Reporter.fatalf Elab_error "non-variable in spine: %s" ([%show: value] other))
      sp_list;
    { dom = List.length sp_list; cod = gamma; ren }
  ;;

  let rec rename (m : metavar) (pr : t) (v : value) : term =
    match force v with
    | Universe l -> Universe l
    | Flex (m', _) when m = m' ->
      Reporter.fatalf
        Elab_error
        "meta variable %s occurs in its own solution"
        ([%show: metavar] m)
    | Flex (m', sp) -> rename_sp m pr (Meta m') sp
    | RigidLocal (l, sp) ->
      (match Hashtbl.find_opt pr.ren l with
       | None ->
         Reporter.fatalf Elab_error "escaping local $%d in meta solution (not in spine)" l
       | Some l' ->
         (* l' is a dom-level; convert to term-side de Bruijn INDEX *)
         rename_sp m pr (LocalVar (pr.dom - l' - 1)) sp)
    | Var (x, sp) -> rename_sp m pr (Var x) sp
    | Label (x, sp) -> rename_sp m pr (Var x) sp
    | IndType (x, sp) -> rename_sp m pr (Var x) sp
    | Elim ({ elim_name; _ }, sp) -> rename_sp m pr (Var elim_name) sp
    | VLambda { name; bound = clos; implicit } ->
      Hashtbl.add pr.ren pr.cod pr.dom;
      let body =
        rename
          m
          { pr with cod = pr.cod + 1; dom = pr.dom + 1 }
          (clos (RigidLocal (pr.cod, Emp)))
      in
      Hashtbl.remove pr.ren pr.cod;
      Lambda { name; implicit; bound = body }
    | VPi ({ name; bound = a; implicit }, b) ->
      let a' = rename m pr a in
      Hashtbl.add pr.ren pr.cod pr.dom;
      let b' =
        rename
          m
          { pr with cod = pr.cod + 1; dom = pr.dom + 1 }
          (b (RigidLocal (pr.cod, Emp)))
      in
      Hashtbl.remove pr.ren pr.cod;
      Pi ({ name; bound = a'; implicit }, b')
    | VLift { from_lvl; to_lvl; ty } -> Lift { from_lvl; to_lvl; ty = rename m pr ty }
    | VLiftTerm { from_lvl; to_lvl; ty; tm } ->
      LiftTerm { from_lvl; to_lvl; ty = rename m pr ty; tm = rename m pr tm }
    | VUnliftTerm { from_lvl; to_lvl; ty; tm } ->
      UnliftTerm { from_lvl; to_lvl; ty = rename m pr ty; tm = rename m pr tm }
    | VRecordType { name; params; fields } ->
      let t_params = List.map (rename m pr) params in
      let rec walk pr = function
        | [] -> []
        | (b : value Syntax.binder) :: rest ->
          let t_bound = rename m pr b.bound in
          Hashtbl.add pr.ren pr.cod pr.dom;
          let pr' = { pr with cod = pr.cod + 1; dom = pr.dom + 1 } in
          let t_rest = walk pr' rest in
          Hashtbl.remove pr.ren pr.cod;
          { Syntax.name = b.name; bound = t_bound; implicit = b.implicit } :: t_rest
      in
      RecordType { name; params = t_params; fields = walk pr fields }
    | VRecordIntro { name; fields } ->
      RecordIntro { name; fields = List.map (fun (f, v) -> f, rename m pr v) fields }
    | VRecordProj (v, f) -> RecordProj { record = rename m pr v; field = f }

  and rename_sp (m : metavar) (pr : t) (t : term) (sp : value bwd) : term =
    match sp with
    | Emp -> t
    | Snoc (sp, u) -> App (rename_sp m pr t sp, rename m pr u)
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
             { name = Printf.sprintf "x%d" (dom - i - 1); implicit = false; bound = acc })
    in
    go 0 tm
  ;;

  let run (gamma : int) (m : metavar) (sp : value bwd) (rhs : value) : value =
    let pr = invert gamma sp in
    let rhs_tm = rename m pr rhs in
    let solution = lams pr.dom rhs_tm in
    Reporter.tracef "solution is: %s" ([%show: term] solution)
    @@ fun () -> eval Emp solution
  ;;
end

let solve (gamma : int) (m : Core.metavar) (sp : Core.value bwd) (rhs : Core.value) : unit
  =
  let spine_str =
    String.concat " <: " @@ List.map (fun v -> [%show: Core.value] v) (Bwd.to_list sp)
  in
  Reporter.tracef "spine: %s" spine_str
  @@ fun () ->
  let solution = PartialRenaming.run gamma m sp rhs in
  Meta.insert_meta m solution
;;

let rec unify ~loc (lvl : int) (a : Core.value) (b : Core.value) : unit =
  Reporter.tracef
    ~loc
    "unify `%s` and `%s`"
    ([%show: Core.value] a)
    ([%show: Core.value] b)
  @@ fun () ->
  (* force_head unfolds metas AND opaque global heads.  After this, the only
     way to still see a Var(x, sp) head is if `x` has no definition (axiom). *)
  match force_head a, force_head b with
  | Universe l1, Universe l2 when Level.equal l1 l2 -> ()
  | VLift a, VLift b ->
    if Level.equal a.from_lvl b.from_lvl && Level.equal a.to_lvl b.to_lvl
    then unify ~loc lvl a.ty b.ty
    else
      Reporter.fatalf
        ~loc
        Type_error
        "cannot unify Lift at different levels: %s vs %s"
        ([%show: Level.level] a.to_lvl)
        ([%show: Level.level] b.to_lvl)
  | VLiftTerm a, VLiftTerm b
    when Level.equal a.from_lvl b.from_lvl && Level.equal a.to_lvl b.to_lvl ->
    unify ~loc lvl a.ty b.ty;
    unify ~loc lvl a.tm b.tm
  | VUnliftTerm a, VUnliftTerm b
    when Level.equal a.from_lvl b.from_lvl && Level.equal a.to_lvl b.to_lvl ->
    unify ~loc lvl a.ty b.ty;
    unify ~loc lvl a.tm b.tm
  | RigidLocal (l1, sp1), RigidLocal (l2, sp2) when l1 = l2 ->
    unify_spine ~loc lvl sp1 sp2
  | Var (h1, sp1), Var (h2, sp2) when String.equal h1 h2 -> unify_spine ~loc lvl sp1 sp2
  | Label (h1, sp1), Label (h2, sp2) when String.equal h1 h2 ->
    unify_spine ~loc lvl sp1 sp2
  | IndType (h1, sp1), IndType (h2, sp2) when String.equal h1 h2 ->
    unify_spine ~loc lvl sp1 sp2
  | Elim (h1, sp1), Elim (h2, sp2) when String.equal h1.elim_name h2.elim_name ->
    unify_spine ~loc lvl sp1 sp2
  | VRecordProj (v1, f1), VRecordProj (v2, f2) when String.equal f1 f2 ->
    unify ~loc lvl v1 v2
  | VLambda { bound = b1; _ }, VLambda { bound = b2; _ } ->
    let x = Core.RigidLocal (lvl, Emp) in
    unify ~loc (lvl + 1) (b1 x) (b2 x)
  | VLambda { bound; _ }, t | t, VLambda { bound; _ } ->
    let x = Core.RigidLocal (lvl, Emp) in
    unify ~loc (lvl + 1) (bound x) (vapp t x)
  (* Record types are equal if they have the same name and equal parameters. *)
  | VRecordType r1, VRecordType r2 when String.equal r1.name r2.name ->
    List.iter2 (unify ~loc lvl) r1.params r2.params
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
         | Some v2 -> unify ~loc lvl v1 v2
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
    solve lvl m sp (VRecordIntro r)
  | VRecordIntro r, t | t, VRecordIntro r ->
    (* One side is a record literal; eta-expand the other by projecting each
       field. The expanded sides are then compared field-by-field. *)
    List.iter
      (fun (f, v_lit) ->
         let v_proj = vrecord_proj t f in
         unify ~loc lvl v_lit v_proj)
      r.fields
  | VPi (_, b1), VPi (_, b2) ->
    let x = Core.RigidLocal (lvl, Emp) in
    unify ~loc (lvl + 1) (b1 x) (b2 x)
  | VPi ({ implicit = true; _ }, b), t | t, VPi ({ implicit = true; _ }, b) ->
    let x = Meta.fresh_meta_value lvl in
    unify ~loc lvl (b x) t
  | Flex (m1, sp1), Flex (m2, sp2) when m1 = m2 -> unify_spine ~loc lvl sp1 sp2
  | t, Flex (m, sp) | Flex (m, sp), t -> solve lvl m sp t
  | expected, actual ->
    Reporter.fatalf
      ~loc
      Type_error
      "cannot unify `%s ?= %s` (or verbose `%s ?= %s`)"
      ([%show: Core.value] expected)
      ([%show: Core.value] actual)
      ([%show: Core.value] a)
      ([%show: Core.value] b)

and unify_spine ~loc (lvl : int) (xs : Core.value bwd) (ys : Core.value bwd) : unit =
  match xs, ys with
  | Emp, Emp -> ()
  | Snoc (xs, x), Snoc (ys, y) ->
    unify_spine ~loc lvl xs ys;
    unify ~loc lvl x y
  | _, _ ->
    let left = String.concat " <: " @@ Bwd.to_list @@ Bwd.map Core.show_value xs in
    let right = String.concat " <: " @@ Bwd.to_list @@ Bwd.map Core.show_value ys in
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
      ; fields = [ "x", Core.VRecordProj (t, "x"); "y", Core.VRecordProj (t, "y") ]
      }
  in
  let result =
    Reporter.run ~emit:(fun _ -> ()) ~fatal:(fun _ -> "FAILED")
    @@ fun () ->
    unify ~loc:(Asai.Range.of_lex_range (Lexing.dummy_pos, Lexing.dummy_pos)) 1 t lit;
    "ok"
  in
  print_endline result;
  [%expect {| ok |}]
;;
