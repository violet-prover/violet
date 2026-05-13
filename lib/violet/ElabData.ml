open Syntax
open Bwd
open Bwd.Infix

(* Give anonymous (`_`) binders unique names so they can be referenced later
   (e.g. as constructor arguments in the eliminator's spine). Leave named
   binders alone — renaming them would invalidate downstream references to
   the original name (the references aren't rewritten). *)
let rename_tele tele : Surface.pretype binder list =
  List.mapi
    (fun i bind ->
       if bind.name = "_" then { bind with name = "_" ^ string_of_int i } else bind)
    tele
;;

let eliminator_params ~name ~params ~deps ~ind_ty =
  let _ = name in
  let _ = ind_ty in
  let good_deps = rename_tele deps in
  params @ good_deps
;;

let eliminator_target_binding ~name ~params ~deps ~ind_ty =
  let params = eliminator_params ~name ~params ~deps ~ind_ty in
  { name = "target"
  ; bound = Surface.apply_tele (Surface.Var name) params
  ; implicit = false
  }
;;

let eliminator_motive_type ~name ~params ~deps ~ind_ty =
  let _ = ind_ty in
  let good_deps = rename_tele deps in
  let final_ty = Surface.apply_tele (Surface.Var name) (params @ good_deps) in
  let final_bind = { name = "_"; bound = final_ty; implicit = false } in
  Surface.pi (good_deps @ [ final_bind ]) Surface.Universe
;;

let eliminator_result_type ~name ~params ~deps ~ind_ty =
  let _ = name in
  let _ = params in
  let _ = ind_ty in
  let good_deps = rename_tele deps in
  let t = Surface.apply_tele (Surface.Var "motive") good_deps in
  Surface.apply t [ Surface.Var "target" ]
;;

let eliminator_case ~name ~params ~deps ~ind_ty (ctor : Surface.pretype binder)
  : Surface.pretype binder
  =
  let _ = deps in
  let _ = ind_ty in
  let rec head = function
    | Surface.App (_, f, _) -> head f
    | Surface.Located { value = t; _ } -> head t
    | t -> t
  in
  let patch_delta delta =
    List.concat_map
      (fun bind ->
         if head bind.bound = Surface.Var name
         then (
           (* Motive takes (deps ... , target), so the IH must mirror that
              shape — supply the recursive point's dep arguments, not just
              the point itself. *)
           let rec_spine = Surface.applied_spine bind.bound in
           let dep_args = List.drop (List.length params) rec_spine in
           [ bind
           ; { name = "ih-" ^ bind.name
             ; bound =
                 Surface.apply
                   (Surface.Var "motive")
                   (dep_args @ [ Surface.Var bind.name ])
             ; implicit = false
             }
           ])
         else [ bind ])
      delta
  in
  let delta = Surface.telescope ctor.bound in
  let renamed_delta = rename_tele delta in
  let spine = Surface.applied_spine (Surface.codomain ctor.bound) in
  (* Implicit params aren't written in the user's surface spine, so only
     drop as many entries as there are explicit params. Dropping
     `List.length params` overshoots whenever any param is implicit
     (e.g. `data Id {A : U} (x : A) : A -> U | refl : Id x x`). *)
  let n_explicit_params = List.length (List.filter (fun p -> not p.implicit) params) in
  let spine = List.drop n_explicit_params spine in
  (* The constructor's stored type is wrapped with implicit data params by
     `close_ctor_type`, so applying it requires those params up front. They
     resolve to the eliminator's outer params (which are in scope here). *)
  let param_args = List.map (fun p -> { p with implicit = true }) params in
  let final = Surface.apply_tele (Surface.Var ctor.name) (param_args @ renamed_delta) in
  { name = "case-" ^ ctor.name
  ; bound =
      Surface.pi
        (patch_delta renamed_delta)
        (Surface.apply (Surface.Var "motive") (spine @ [ final ]))
  ; implicit = false
  }
;;

let eliminator_type ~name ~params ~deps ~ind_ty ctors =
  let elim_params = eliminator_params ~name ~params ~deps ~ind_ty in
  let target_bind = eliminator_target_binding ~name ~params ~deps ~ind_ty in
  let motive_type = eliminator_motive_type ~name ~params ~deps ~ind_ty in
  let case_binds =
    List.map (fun c -> eliminator_case ~name ~params ~deps ~ind_ty c) ctors
  in
  let result_ty = eliminator_result_type ~name ~params ~deps ~ind_ty in
  Surface.pi
    (elim_params
     @ [ target_bind; { name = "motive"; bound = motive_type; implicit = false } ]
     @ case_binds)
    result_ty
;;

let%expect_test "`data List (A : U) : U`, the generated eliminator will rely on A" =
  let result =
    eliminator_params
      ~name:"List"
      ~params:[ { name = "A"; bound = Surface.Universe; implicit = false } ]
      ~deps:[]
      ~ind_ty:Surface.Universe
  in
  print_string @@ [%show: Surface.pretype binder list] result;
  [%expect {| [{ Syntax.name = "A"; bound = 𝓤; implicit = false }] |}]
;;

let%expect_test "List target has type `List A`" =
  let result =
    eliminator_target_binding
      ~name:"List"
      ~params:[ { name = "A"; bound = Surface.Universe; implicit = false } ]
      ~deps:[]
      ~ind_ty:Surface.Universe
  in
  print_string @@ [%show: Surface.pretype binder] result;
  [%expect {| { Syntax.name = "target"; bound = (List A); implicit = false } |}]
;;

let%expect_test "Vec motive" =
  let result =
    eliminator_motive_type
      ~name:"Vec"
      ~params:[ { name = "A"; bound = Surface.Universe; implicit = false } ]
      ~deps:[ { name = "_"; bound = Surface.Var "Nat"; implicit = false } ]
      ~ind_ty:Surface.Universe
  in
  print_string @@ [%show: Surface.pretype] result;
  [%expect {| Π(_0 : Nat) -> Π(_ : ((Vec A) _0)) -> 𝓤 |}]
;;

let%expect_test "Vec case nil" =
  let result =
    eliminator_case
      ~name:"Vec"
      ~params:[ { name = "A"; bound = Surface.Universe; implicit = false } ]
      ~deps:[ { name = "_"; bound = Surface.Var "Nat"; implicit = false } ]
      ~ind_ty:Surface.Universe
      { name = "nil"
      ; bound = Surface.apply (Surface.Var "Vec") [ Surface.Var "A"; Surface.Var "zero" ]
      ; implicit = false
      }
  in
  print_string @@ [%show: Surface.pretype binder] result;
  [%expect
    {|
    { Syntax.name = "case-nil"; bound = ((motive zero) (nil {A}));
      implicit = false }
    |}]
;;

let%expect_test "Vec case cons" =
  let result =
    eliminator_case
      ~name:"Vec"
      ~params:[ { name = "A"; bound = Surface.Universe; implicit = false } ]
      ~deps:[ { name = "_"; bound = Surface.Var "Nat"; implicit = false } ]
      ~ind_ty:Surface.Universe
      { name = "cons"
      ; bound =
          Surface.pi
            [ { name = "k"; bound = Surface.Var "Nat"; implicit = true }
            ; { name = "x"; bound = Surface.Var "A"; implicit = false }
            ; { name = "xs"
              ; bound =
                  Surface.apply (Surface.Var "Vec") [ Surface.Var "A"; Surface.Var "k" ]
              ; implicit = false
              }
            ]
            (Surface.apply
               (Surface.Var "Vec")
               [ Surface.Var "A"; Surface.apply (Surface.Var "suc") [ Surface.Var "k" ] ])
      ; implicit = false
      }
  in
  print_string @@ [%show: Surface.pretype binder] result;
  [%expect
    {|
    { Syntax.name = "case-cons";
      bound =
      Π{k : Nat} -> Π(x : A) -> Π(xs : ((Vec A) k)) -> Π(ih-xs : ((motive k) xs)) -> ((motive (suc k)) ((((cons {A}) {k}) x) xs));
      implicit = false }
    |}]
;;

let%expect_test "Vec result type" =
  let result =
    eliminator_result_type
      ~name:"Vec"
      ~params:[ { name = "A"; bound = Surface.Universe; implicit = false } ]
      ~deps:[ { name = "_"; bound = Surface.Var "Nat"; implicit = false } ]
      ~ind_ty:Surface.Universe
  in
  print_string @@ [%show: Surface.pretype] result;
  [%expect {| ((motive _0) target) |}]
;;

(* Per-ctor binder kind, computed at declaration time. *)
type binder_kind =
  | Regular
  | Recursive of string list (* names of dep args extracted from rec arg's type *)

type ctor_info =
  { ctor_name : string
  ; binder_names : string list (* renamed ctor own arg names *)
  ; binder_kinds : binder_kind list
  }

let rec head_of_surface = function
  | Surface.App (_, f, _) -> head_of_surface f
  | Surface.Located { value = t; _ } -> head_of_surface t
  | t -> t
;;

let analyze_ctor ~ind_name ~params (ctor : Surface.pretype binder) : ctor_info =
  let delta = rename_tele (Surface.telescope ctor.bound) in
  let n_explicit_params =
    List.length (List.filter (fun (p : Surface.pretype binder) -> not p.implicit) params)
  in
  let kinds =
    List.map
      (fun (b : Surface.pretype binder) ->
         if head_of_surface b.bound = Surface.Var ind_name
         then (
           let rec_spine = Surface.applied_spine b.bound in
           let dep_args = List.drop n_explicit_params rec_spine in
           let dep_names =
             List.map
               (fun a ->
                  match a with
                  | Surface.Var n -> n
                  | Surface.Located { value = Surface.Var n; _ } -> n
                  | _ -> "_")
               dep_args
           in
           Recursive dep_names)
         else Regular)
      delta
  in
  { ctor_name = ctor.name
  ; binder_names = List.map (fun b -> b.name) delta
  ; binder_kinds = kinds
  }
;;

(* vapp specialized for the heads we may encounter: VLambda closures (real
   case binders post-elaboration) and Var/Label/etc. with spines. Mirrors
   Evaluation.vapp but is kept local to avoid module cycles. *)
let vapp (t : Core.value) (u : Core.value) : Core.value =
  match t with
  | Core.VLambda { bound = f; _ } -> f u
  | Core.Var (h, sp) -> Core.Var (h, sp <: u)
  | Core.Label (h, sp) -> Core.Label (h, sp <: u)
  | Core.Flex (m, sp) -> Core.Flex (m, sp <: u)
  | Core.RigidLocal (l, sp) -> Core.RigidLocal (l, sp <: u)
  | Core.IndType (h, sp) -> Core.IndType (h, sp <: u)
  | v -> Reporter.fatalf Elab_error "ι-reduction: cannot apply %s" ([%show: Core.value] v)
;;

let vapp_list t args = List.fold_left vapp t args

let build_elim_reducer
      ~(ind_name : string)
      ~(elim_name : string)
      ~(params : Surface.pretype binder list)
      ~(deps : Surface.pretype binder list)
      (ctors : Surface.pretype binder list)
  : Core.value bwd -> Core.value option
  =
  let n_params = List.length params in
  let n_deps = List.length deps in
  let n_data_params = n_params in
  let target_idx = n_params + n_deps in
  let motive_idx = target_idx + 1 in
  let cases_start = motive_idx + 1 in
  let n_structural = cases_start + List.length ctors in
  let ctor_infos = List.map (analyze_ctor ~ind_name ~params) ctors in
  let find_ctor_index name =
    let rec go xs i =
      match xs with
      | [] -> None
      | info :: _ when info.ctor_name = name -> Some i
      | _ :: rest -> go rest (i + 1)
    in
    go ctor_infos 0
  in
  fun (spine : Core.value bwd) ->
    let spine_list = Bwd.to_list spine in
    (* Need at least the structural part filled to reduce.  Extra args past
       the structural slice are trailing applications to the eliminator's
       result and are applied after reduction. *)
    if List.length spine_list < n_structural
    then None
    else (
      let structural = List.filteri (fun j _ -> j < n_structural) spine_list in
      let trailing = List.filteri (fun j _ -> j >= n_structural) spine_list in
      match List.nth_opt structural target_idx with
      | Some (Core.Label (ctor_name, label_sp)) ->
        (match find_ctor_index ctor_name with
         | None -> None
         | Some i ->
           let info = List.nth ctor_infos i in
           let label_list = Bwd.to_list label_sp in
           let own_args = List.drop n_data_params label_list in
           let env = List.combine info.binder_names own_args in
           let lookup_dep name =
             match List.assoc_opt name env with
             | Some v -> v
             | None ->
               Reporter.fatalf Elab_error "ι-reduction: unknown dep name `%s`" name
           in
           let params_sp = List.filteri (fun j _ -> j < n_params) structural in
           let cases_sp = List.filteri (fun j _ -> j >= cases_start) structural in
           let motive = List.nth structural motive_idx in
           let case = List.nth structural (cases_start + i) in
           let case_args =
             List.concat_map
               (fun (arg, kind) ->
                  match kind with
                  | Regular -> [ arg ]
                  | Recursive dep_names ->
                    let ih_deps = List.map lookup_dep dep_names in
                    let ih_spine =
                      Bwd.of_list (params_sp @ ih_deps @ [ arg; motive ] @ cases_sp)
                    in
                    [ arg; Core.Var (elim_name, ih_spine) ])
               (List.combine own_args info.binder_kinds)
           in
           Some (vapp_list (vapp_list case case_args) trailing))
      | _ -> None)
;;

let nat_ctors : Surface.pretype binder list =
  [ { name = "zero"; bound = Surface.Var "Nat"; implicit = false }
  ; { name = "suc"
    ; bound =
        Surface.Pi
          ({ name = "_"; bound = Surface.Var "Nat"; implicit = false }, Surface.Var "Nat")
    ; implicit = false
    }
  ]
;;

let%expect_test "Nat-elim reduces target=zero to case-zero" =
  let reducer =
    build_elim_reducer ~ind_name:"Nat" ~elim_name:"Nat-elim" ~params:[] ~deps:[] nat_ctors
  in
  let target = Core.Label ("zero", Emp) in
  let motive = Core.Universe in
  let cz = Core.Var ("cz", Emp) in
  let cs = Core.Var ("cs", Emp) in
  let spine = Emp <: target <: motive <: cz <: cs in
  print_string @@ [%show: Core.value option] (reducer spine);
  [%expect {| (Some cz) |}]
;;

let%expect_test "Nat-elim reduces target=suc n to (case-suc n IH)" =
  let reducer =
    build_elim_reducer ~ind_name:"Nat" ~elim_name:"Nat-elim" ~params:[] ~deps:[] nat_ctors
  in
  let n = Core.Var ("n", Emp) in
  let target = Core.Label ("suc", Emp <: n) in
  let motive = Core.Var ("M", Emp) in
  let cz = Core.Var ("cz", Emp) in
  let cs = Core.Var ("cs", Emp) in
  let spine = Emp <: target <: motive <: cz <: cs in
  print_string @@ [%show: Core.value option] (reducer spine);
  [%expect {| (Some cs n (Nat-elim n M cz cs)) |}]
;;

let vec_ctors : Surface.pretype binder list =
  [ { name = "nil"
    ; bound = Surface.apply (Surface.Var "Vec") [ Surface.Var "A"; Surface.Var "zero" ]
    ; implicit = false
    }
  ; { name = "cons"
    ; bound =
        Surface.pi
          [ { name = "n"; bound = Surface.Var "Nat"; implicit = true }
          ; { name = "_"; bound = Surface.Var "A"; implicit = false }
          ; { name = "_"
            ; bound =
                Surface.apply (Surface.Var "Vec") [ Surface.Var "A"; Surface.Var "n" ]
            ; implicit = false
            }
          ]
          (Surface.apply
             (Surface.Var "Vec")
             [ Surface.Var "A"; Surface.apply (Surface.Var "suc") [ Surface.Var "n" ] ])
    ; implicit = false
    }
  ]
;;

let%expect_test "Vec-elim reduces target=cons {A}{k} x xs to case-cons k x xs IH" =
  let reducer =
    build_elim_reducer
      ~ind_name:"Vec"
      ~elim_name:"Vec-elim"
      ~params:[ { name = "A"; bound = Surface.Universe; implicit = false } ]
      ~deps:[ { name = "_"; bound = Surface.Var "Nat"; implicit = false } ]
      vec_ctors
  in
  let aV = Core.Var ("A", Emp) in
  let kV = Core.Var ("k", Emp) in
  let xV = Core.Var ("x", Emp) in
  let xsV = Core.Var ("xs", Emp) in
  let target = Core.Label ("cons", Emp <: aV <: kV <: xV <: xsV) in
  let depN = Core.Var ("idx", Emp) in
  let motive = Core.Var ("M", Emp) in
  let cnil = Core.Var ("cnil", Emp) in
  let ccons = Core.Var ("ccons", Emp) in
  let spine = Emp <: aV <: depN <: target <: motive <: cnil <: ccons in
  print_string @@ [%show: Core.value option] (reducer spine);
  [%expect {| (Some ccons k x xs (Vec-elim A k xs M cnil ccons)) |}]
;;
