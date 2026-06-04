open Violet_surface
open Violet_common
module Syntax = Violet_kernel.Syntax
module Context_view = Violet_kernel.Context_view
module Pretty = Violet_kernel.Pretty
module Level = Violet_kernel.Level
module Evaluation = Wiring.Eval
open Syntax
open Surface_utils

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

(* Build the ctor -> owner mapping used by [readback_value_to_surface] to
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
      (fun (d : Surface.pretype Surface.sbinder) ->
         match (head_of_surface d.bound).Surface.node with
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
  let at node : Surface.preterm = Surface.Mk.at loc node in
  let rb t = core_term_to_surface ~loc ~cv ~owner_map t in
  match t with
  | Core.Universe _ -> at Surface.Universe
  | Core.LocalVar ix ->
    let lvl = Context_view.lvl cv - 1 - ix in
    (match Context_view.nth_name_from_lvl cv lvl with
     | Some name -> at (Surface.Var [ name ])
     | None ->
       Reporter.fatalf
         ~loc
         Elab_error
         "elim: index readback hit unknown local index %d"
         ix)
  | Core.Var n ->
    (match List.assoc_opt n owner_map with
     | Some owner -> at (Surface.Var [ owner; n ])
     | None -> at (Surface.Var [ n ]))
  | Core.App _ ->
    let rec collect_spine acc = function
      | Core.App (f, a, _) -> collect_spine (a :: acc) f
      | head -> head, acc
    in
    let head, spine = collect_spine [] t in
    let imps =
      match head with
      | Core.Var x ->
        let ind_imps =
          match Context.S.resolve [ x ] with
          | Some (_, `Inductive info) ->
            let pi =
              List.map (fun (p : _ Surface.sbinder) -> p.implicit) info.params
            in
            let di = List.map (fun (d : _ Surface.sbinder) -> d.implicit) info.deps in
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
                   (fun (c : _ Surface.sbinder) ->
                      Syntax.Name.to_string c.name.Surface.value = x)
                   info.ctors
               in
               let binder_imps =
                 match ctor_opt with
                 | Some c ->
                   List.map
                     (fun (b : _ Surface.sbinder) -> b.implicit)
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
         let imp =
           match List.nth_opt imps i with
           | Some v -> v
           | None -> false
         in
         at (Surface.App (imp, acc, rb arg)), i + 1)
      (head_s, 0)
      spine
    |> fst
  | Core.Lambda { name; bound; implicit } ->
    let ns = Syntax.Name.to_string name in
    let cv' = Context_view.extend cv ns in
    at
      (Surface.Lambda
         { name = { Surface.loc; value = name }
         ; bound = core_term_to_surface ~loc ~cv:cv' ~owner_map bound
         ; implicit
         })
  | Core.TypedLambda ({ name; bound; implicit }, body) ->
    let ns = Syntax.Name.to_string name in
    let cv' = Context_view.extend cv ns in
    at
      (Surface.TypedLambda
         ( { name = { Surface.loc; value = name }; bound = rb bound; implicit }
         , core_term_to_surface ~loc ~cv:cv' ~owner_map body ))
  | Core.Pi ({ name; bound; implicit }, body) ->
    let ns = Syntax.Name.to_string name in
    let cv' = Context_view.extend cv ns in
    at
      (Surface.Pi
         ( { name = { Surface.loc; value = name }; bound = rb bound; implicit }
         , core_term_to_surface ~loc ~cv:cv' ~owner_map body ))
  | Core.Meta _ | Core.InsertedMeta _ -> at Surface.Hole
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
    at (Surface.RecordLit (List.map (fun (f, e) -> { Surface.loc; value = f }, rb e) fields))
  | Core.RecordProj { record; field } ->
    at (Surface.Proj (rb record, { Surface.loc; value = field }))
  | Core.IdAbsurd t -> at (Surface.IdAbsurd (rb t))
  | Core.Empty -> at (Surface.Var [ "Empty" ])
  | Core.Absurd t -> at (Surface.Absurd (rb t))
;;

let%expect_test "core_term_to_surface: Universe" =
  let loc = Surface.dummy_loc in
  let cv = Context_view.empty in
  let result = core_term_to_surface ~loc ~cv ~owner_map:[] (Core.Universe Level.LZero) in
  print_string (Surface.show_preterm result);
  [%expect {| 𝓤 |}]
;;

let%expect_test "core_term_to_surface: LocalVar renders binder name" =
  let loc = Surface.dummy_loc in
  let cv = Context_view.extend Context_view.empty "x" in
  let result = core_term_to_surface ~loc ~cv ~owner_map:[] (Core.LocalVar 0) in
  print_string (Surface.show_preterm result);
  [%expect {| x |}]
;;

let%expect_test "core_term_to_surface: Lambda preserves binder name" =
  let loc = Surface.dummy_loc in
  let cv = Context_view.empty in
  let tm = Core.Lambda { name = Named "y"; bound = Core.LocalVar 0; implicit = false } in
  let result = core_term_to_surface ~loc ~cv ~owner_map:[] tm in
  print_string (Surface.show_preterm result);
  [%expect {| fun y => y |}]
;;

let%expect_test "core_term_to_surface: Meta becomes Hole" =
  let loc = Surface.dummy_loc in
  let cv = Context_view.empty in
  let result = core_term_to_surface ~loc ~cv ~owner_map:[] (Core.Meta (Core.MetaVar 0)) in
  print_string (Surface.show_preterm result);
  [%expect {| _ |}]
;;

let%expect_test "core_term_to_surface: Var with owner_map qualifies" =
  let loc = Surface.dummy_loc in
  let cv = Context_view.empty in
  let owner_map = [ "zero", "Nat"; "suc", "Nat" ] in
  let result = core_term_to_surface ~loc ~cv ~owner_map (Core.Var "zero") in
  print_string (Surface.show_preterm result);
  [%expect {| Nat/zero |}]
;;

let%expect_test "core_term_to_surface: RecordIntro" =
  let loc = Surface.dummy_loc in
  let cv = Context_view.empty in
  let tm =
    Core.RecordIntro
      { name = "Pair"; fields = [ "fst", Core.Var "a"; "snd", Core.Var "b" ] }
  in
  let result = core_term_to_surface ~loc ~cv ~owner_map:[] tm in
  print_string (Surface.show_preterm result);
  [%expect {| { fst = a, snd = b } |}]
;;

let%expect_test "core_term_to_surface: RecordProj" =
  let loc = Surface.dummy_loc in
  let cv = Context_view.empty in
  let tm = Core.RecordProj { record = Core.Var "p"; field = "x" } in
  let result = core_term_to_surface ~loc ~cv ~owner_map:[] tm in
  print_string (Surface.show_preterm result);
  [%expect {| p.x |}]
;;

let%expect_test "cv_of_user_level_names builds correct context" =
  let cv = cv_of_user_level_names [ 0, "n"; 1, "m" ] in
  Printf.printf "lvl=%d" (Context_view.lvl cv);
  [%expect {| lvl=2 |}]
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
