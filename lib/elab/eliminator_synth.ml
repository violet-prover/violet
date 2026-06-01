open Violet_surface
open Violet_common
module Syntax = Violet_kernel.Syntax
module Level = Violet_kernel.Level
module Context_view = Violet_kernel.Context_view
module Pretty = Violet_kernel.Pretty
module Evaluation = Wiring.Eval
open Syntax
open Bwd
open Bwd.Infix
open Surface_utils

(* Give anonymous binders unique names so they can be referenced later
   (e.g. as constructor arguments in the eliminator's spine). Leave named
   binders alone — renaming them would invalidate downstream references to
   the original name (the references aren't rewritten). *)
let rename_tele tele : Surface.pretype binder list =
  List.mapi
    (fun i bind ->
       match bind.name with
       | Anon -> { bind with name = Named (Printf.sprintf "_%d" i) }
       | Named _ -> bind)
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
  { name = Named "target"
  ; bound = Surface.apply_tele (Surface.Var [ name ]) params
  ; implicit = false
  }
;;

let eliminator_motive_type ~name ~params ~deps ~ind_ty =
  let good_deps = rename_tele deps in
  let final_ty = Surface.apply_tele (Surface.Var [ name ]) (params @ good_deps) in
  let final_bind = { name = Anon; bound = final_ty; implicit = false } in
  Surface.pi (good_deps @ [ final_bind ]) ind_ty
;;

let eliminator_result_type ~name ~params ~deps ~ind_ty =
  let _ = name in
  let _ = params in
  let _ = ind_ty in
  let good_deps = rename_tele deps in
  let t = Surface.apply_tele (Surface.Var [ "motive" ]) good_deps in
  Surface.apply t [ Surface.Var [ "target" ] ]
;;

let eliminator_case ~name ~params ~deps ~ind_ty (ctor : Surface.pretype binder)
  : Surface.pretype binder
  =
  let _ = deps in
  let _ = ind_ty in
  let patch_delta delta =
    List.concat_map
      (fun bind ->
         if head_of_surface bind.bound = Surface.Var [ name ]
         then (
           (* Motive takes (deps ... , target), so the IH must mirror that
              shape — supply the recursive point's dep arguments, not just
              the point itself. *)
           let rec_spine = Surface.applied_spine bind.bound in
           let dep_args = List.drop (List.length params) rec_spine in
           [ bind
           ; { name = Named ("ih-" ^ Name.to_string bind.name)
             ; bound =
                 Surface.apply
                   (Surface.Var [ "motive" ])
                   (dep_args @ [ Surface.Var [ Name.to_string bind.name ] ])
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
  let final =
    Surface.apply_tele
      (Surface.Var [ name; Name.to_string ctor.name ])
      (param_args @ renamed_delta)
  in
  { name = Named ("case-" ^ Name.to_string ctor.name)
  ; bound =
      Surface.pi
        (patch_delta renamed_delta)
        (Surface.apply (Surface.Var [ "motive" ]) (spine @ [ final ]))
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
     @ [ target_bind; { name = Named "motive"; bound = motive_type; implicit = false } ]
     @ case_binds)
    result_ty
;;

let%expect_test "`data List (A : U) : U`, the generated eliminator will rely on A" =
  let result =
    eliminator_params
      ~name:"List"
      ~params:[ { name = Named "A"; bound = Surface.Universe; implicit = false } ]
      ~deps:[]
      ~ind_ty:Surface.Universe
  in
  print_string @@ [%show: Surface.pretype binder list] result;
  [%expect {| [{ Syntax.name = (Syntax.Named "A"); bound = 𝓤; implicit = false }] |}]
;;

let%expect_test "List target has type `List A`" =
  let result =
    eliminator_target_binding
      ~name:"List"
      ~params:[ { name = Named "A"; bound = Surface.Universe; implicit = false } ]
      ~deps:[]
      ~ind_ty:Surface.Universe
  in
  print_string @@ [%show: Surface.pretype binder] result;
  [%expect
    {| { Syntax.name = (Syntax.Named "target"); bound = (List A); implicit = false } |}]
;;

let%expect_test "Vec motive" =
  let result =
    eliminator_motive_type
      ~name:"Vec"
      ~params:[ { name = Named "A"; bound = Surface.Universe; implicit = false } ]
      ~deps:[ { name = Anon; bound = Surface.Var [ "Nat" ]; implicit = false } ]
      ~ind_ty:Surface.Universe
  in
  print_string @@ [%show: Surface.pretype] result;
  [%expect {| Π(_0 : Nat) -> Π(_ : ((Vec A) _0)) -> 𝓤 |}]
;;

let%expect_test "Vec case nil" =
  let result =
    eliminator_case
      ~name:"Vec"
      ~params:[ { name = Named "A"; bound = Surface.Universe; implicit = false } ]
      ~deps:[ { name = Anon; bound = Surface.Var [ "Nat" ]; implicit = false } ]
      ~ind_ty:Surface.Universe
      { name = Named "nil"
      ; bound =
          Surface.apply
            (Surface.Var [ "Vec" ])
            [ Surface.Var [ "A" ]; Surface.Var [ "zero" ] ]
      ; implicit = false
      }
  in
  print_string @@ [%show: Surface.pretype binder] result;
  [%expect
    {|
    { Syntax.name = (Syntax.Named "case-nil");
      bound = ((motive zero) (Vec/nil {A})); implicit = false }
    |}]
;;

let%expect_test "Vec case cons" =
  let result =
    eliminator_case
      ~name:"Vec"
      ~params:[ { name = Named "A"; bound = Surface.Universe; implicit = false } ]
      ~deps:[ { name = Anon; bound = Surface.Var [ "Nat" ]; implicit = false } ]
      ~ind_ty:Surface.Universe
      { name = Named "cons"
      ; bound =
          Surface.pi
            [ { name = Named "k"; bound = Surface.Var [ "Nat" ]; implicit = true }
            ; { name = Named "x"; bound = Surface.Var [ "A" ]; implicit = false }
            ; { name = Named "xs"
              ; bound =
                  Surface.apply
                    (Surface.Var [ "Vec" ])
                    [ Surface.Var [ "A" ]; Surface.Var [ "k" ] ]
              ; implicit = false
              }
            ]
            (Surface.apply
               (Surface.Var [ "Vec" ])
               [ Surface.Var [ "A" ]
               ; Surface.apply (Surface.Var [ "suc" ]) [ Surface.Var [ "k" ] ]
               ])
      ; implicit = false
      }
  in
  print_string @@ [%show: Surface.pretype binder] result;
  [%expect
    {|
    { Syntax.name = (Syntax.Named "case-cons");
      bound =
      Π{k : Nat} -> Π(x : A) -> Π(xs : ((Vec A) k)) -> Π(ih-xs : ((motive k) xs)) -> ((motive (suc k)) ((((Vec/cons {A}) {k}) x) xs));
      implicit = false }
    |}]
;;

let%expect_test "Vec result type" =
  let result =
    eliminator_result_type
      ~name:"Vec"
      ~params:[ { name = Named "A"; bound = Surface.Universe; implicit = false } ]
      ~deps:[ { name = Anon; bound = Surface.Var [ "Nat" ]; implicit = false } ]
      ~ind_ty:Surface.Universe
  in
  print_string @@ [%show: Surface.pretype] result;
  [%expect {| ((motive _0) target) |}]
;;

let arities_of (info : Context.ind_info) : (string * int) list =
  List.map
    (fun (ci : Context.ctor_info) -> ci.ctor_name, List.length ci.binder_names)
    info.infos
;;

let case_arg_lambda_binders
      ~(prefix : string)
      ~(ind_name : string)
      (c : Surface.pretype binder)
  : string list * string list
  =
  let delta = rename_tele (Surface.telescope c.bound) in
  let lambdas = ref [] in
  let fields = ref [] in
  List.iter
    (fun (b : Surface.pretype binder) ->
       let n = prefix ^ Name.to_string b.name in
       fields := n :: !fields;
       lambdas := n :: !lambdas;
       if head_of_surface b.bound = Surface.Var [ ind_name ]
       then lambdas := (prefix ^ "ih-" ^ Name.to_string b.name) :: !lambdas)
    delta;
  List.rev !lambdas, List.rev !fields
;;

let analyze_ctor ~ind_name ~params (ctor : Surface.pretype binder) : Context.ctor_info =
  let delta = rename_tele (Surface.telescope ctor.bound) in
  let n_explicit_params =
    List.length (List.filter (fun (p : Surface.pretype binder) -> not p.implicit) params)
  in
  let kinds =
    List.map
      (fun (b : Surface.pretype binder) ->
         if head_of_surface b.bound = Surface.Var [ ind_name ]
         then (
           let rec_spine = Surface.applied_spine b.bound in
           let dep_args = List.drop n_explicit_params rec_spine in
           let dep_names =
             List.map
               (fun a ->
                  match a with
                  | Surface.Var [ n ] -> n
                  | Surface.Located { value = Surface.Var [ n ]; _ } -> n
                  | _ -> "_")
               dep_args
           in
           Context.Recursive dep_names)
         else Context.Regular)
      delta
  in
  { ctor_name = Name.to_string ctor.name
  ; binder_names = List.map (fun b -> Name.to_string b.name) delta
  ; binder_kinds = kinds
  }
;;

(* vapp specialized for the heads we may encounter: VLambda closures (real
   case binders post-elaboration) and Var/Label/etc. with spines. Mirrors
   Evaluation.vapp but is kept local to avoid module cycles. *)
let vapp (t : Core.value) (u : Core.value) : Core.value =
  let arg = Core.explicit_arg u in
  match t with
  | Core.VLambda { bound = f; _ } -> f u
  | Core.Var (h, sp) -> Core.Var (h, sp <: arg)
  | Core.Label (h, sp) -> Core.Label (h, sp <: arg)
  | Core.Flex (m, sp) -> Core.Flex (m, sp <: arg)
  | Core.RigidLocal (l, sp) -> Core.RigidLocal (l, sp <: arg)
  | Core.IndType (h, sp) -> Core.IndType (h, sp <: arg)
  | v ->
    Reporter.fatalf
      Elab_error
      "ι-reduction: cannot apply %s"
      (Pretty.pp_term Context_view.empty (Evaluation.quote 0 v))
;;

let vapp_list t args = List.fold_left vapp t args

let build_elim_reducer
      ~(ind_name : string)
      ~(elim_name : string)
      ~(params : Surface.pretype binder list)
      ~(deps : Surface.pretype binder list)
      (ctors : Surface.pretype binder list)
  : Core.spine -> Core.value option
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
      | (info : Context.ctor_info) :: _ when info.ctor_name = name -> Some i
      | _ :: rest -> go rest (i + 1)
    in
    go ctor_infos 0
  in
  (* `let rec` so the IH for a recursive ctor position can build another
     `Elim` whose head carries this very reducer. *)
  let rec reducer (spine : Core.spine) : Core.value option =
    let spine_list = Bwd.to_list (Core.spine_values spine) in
    (* Need at least the structural part filled to reduce.  Extra args past
       the structural slice are trailing applications to the eliminator's
       result and are applied after reduction. *)
    if List.length spine_list < n_structural
    then None
    else (
      let structural = List.filteri (fun j _ -> j < n_structural) spine_list in
      let trailing = List.filteri (fun j _ -> j >= n_structural) spine_list in
      let target = List.nth_opt structural target_idx in
      match Option.map Evaluation.force_head target with
      | Some (Core.Label (ctor_name, label_sp)) ->
        (match find_ctor_index ctor_name with
         | None -> None
         | Some i ->
           let info =
             match List.nth_opt ctor_infos i with
             | Some v -> v
             | None ->
               Reporter.fatalf
                 Elab_error
                 "internal: iota-reduction for `%s/elim`: ctor info index %d out of \
                  bounds (len=%d)"
                 ind_name
                 i
                 (List.length ctor_infos)
           in
           let label_list = Bwd.to_list (Core.spine_values label_sp) in
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
           let motive =
             match List.nth_opt structural motive_idx with
             | Some v -> v
             | None ->
               Reporter.fatalf
                 Elab_error
                 "internal: iota-reduction for `%s/elim`: motive index %d out of bounds \
                  (structural len=%d)"
                 ind_name
                 motive_idx
                 (List.length structural)
           in
           let case =
             match List.nth_opt structural (cases_start + i) with
             | Some v -> v
             | None ->
               Reporter.fatalf
                 Elab_error
                 "internal: iota-reduction for `%s/elim`: case index %d out of bounds \
                  (structural len=%d)"
                 ind_name
                 (cases_start + i)
                 (List.length structural)
           in
           let case_args =
             List.concat_map
               (fun (arg, kind) ->
                  match (kind : Context.binder_kind) with
                  | Context.Regular -> [ arg ]
                  | Context.Recursive dep_names ->
                    let ih_deps = List.map lookup_dep dep_names in
                    let ih_spine =
                      Bwd.of_list
                        (List.map
                           Core.explicit_arg
                           (params_sp @ ih_deps @ [ arg; motive ] @ cases_sp))
                    in
                    [ arg; Core.Elim ({ elim_name; reducer }, ih_spine) ])
               (List.combine own_args info.binder_kinds)
           in
           Some (vapp_list (vapp_list case case_args) trailing))
      | _ -> None)
  in
  reducer
;;

let nat_ctors : Surface.pretype binder list =
  [ { name = Named "zero"; bound = Surface.Var [ "Nat" ]; implicit = false }
  ; { name = Named "suc"
    ; bound =
        Surface.Pi
          ( { name = Anon; bound = Surface.Var [ "Nat" ]; implicit = false }
          , Surface.Var [ "Nat" ] )
    ; implicit = false
    }
  ]
;;

let%expect_test "Nat-elim reduces target=zero to case-zero" =
  let reducer =
    build_elim_reducer ~ind_name:"Nat" ~elim_name:"Nat/elim" ~params:[] ~deps:[] nat_ctors
  in
  let target = Core.Label ("zero", Emp) in
  let motive = Core.Universe Level.LZero in
  let cz = Core.Var ("cz", Emp) in
  let cs = Core.Var ("cs", Emp) in
  let spine =
    Emp
    <: Core.explicit_arg target
    <: Core.explicit_arg motive
    <: Core.explicit_arg cz
    <: Core.explicit_arg cs
  in
  (print_string
   @@
   match reducer spine with
   | None -> "None"
   | Some v -> "(Some " ^ Pretty.pp_value Context_view.empty v ^ ")");
  [%expect {| (Some cz) |}]
;;

let%expect_test "Nat-elim reduces target=suc n to (case-suc n IH)" =
  let reducer =
    build_elim_reducer ~ind_name:"Nat" ~elim_name:"Nat/elim" ~params:[] ~deps:[] nat_ctors
  in
  let n = Core.Var ("n", Emp) in
  let target = Core.Label ("suc", Emp <: Core.explicit_arg n) in
  let motive = Core.Var ("M", Emp) in
  let cz = Core.Var ("cz", Emp) in
  let cs = Core.Var ("cs", Emp) in
  let spine =
    Emp
    <: Core.explicit_arg target
    <: Core.explicit_arg motive
    <: Core.explicit_arg cz
    <: Core.explicit_arg cs
  in
  (print_string
   @@
   match reducer spine with
   | None -> "None"
   | Some v -> "(Some " ^ Pretty.pp_value Context_view.empty v ^ ")");
  [%expect {| (Some cs n (Nat/elim n M cz cs)) |}]
;;

let vec_ctors : Surface.pretype binder list =
  [ { name = Named "nil"
    ; bound =
        Surface.apply
          (Surface.Var [ "Vec" ])
          [ Surface.Var [ "A" ]; Surface.Var [ "zero" ] ]
    ; implicit = false
    }
  ; { name = Named "cons"
    ; bound =
        Surface.pi
          [ { name = Named "n"; bound = Surface.Var [ "Nat" ]; implicit = true }
          ; { name = Anon; bound = Surface.Var [ "A" ]; implicit = false }
          ; { name = Anon
            ; bound =
                Surface.apply
                  (Surface.Var [ "Vec" ])
                  [ Surface.Var [ "A" ]; Surface.Var [ "n" ] ]
            ; implicit = false
            }
          ]
          (Surface.apply
             (Surface.Var [ "Vec" ])
             [ Surface.Var [ "A" ]
             ; Surface.apply (Surface.Var [ "suc" ]) [ Surface.Var [ "n" ] ]
             ])
    ; implicit = false
    }
  ]
;;

let%expect_test "Vec-elim reduces target=cons {A}{k} x xs to case-cons k x xs IH" =
  let reducer =
    build_elim_reducer
      ~ind_name:"Vec"
      ~elim_name:"Vec/elim"
      ~params:[ { name = Named "A"; bound = Surface.Universe; implicit = false } ]
      ~deps:[ { name = Anon; bound = Surface.Var [ "Nat" ]; implicit = false } ]
      vec_ctors
  in
  let aV = Core.Var ("A", Emp) in
  let kV = Core.Var ("k", Emp) in
  let xV = Core.Var ("x", Emp) in
  let xsV = Core.Var ("xs", Emp) in
  let target =
    Core.Label
      ( "cons"
      , Emp
        <: Core.explicit_arg aV
        <: Core.explicit_arg kV
        <: Core.explicit_arg xV
        <: Core.explicit_arg xsV )
  in
  let depN = Core.Var ("idx", Emp) in
  let motive = Core.Var ("M", Emp) in
  let cnil = Core.Var ("cnil", Emp) in
  let ccons = Core.Var ("ccons", Emp) in
  let spine =
    Emp
    <: Core.explicit_arg aV
    <: Core.explicit_arg depN
    <: Core.explicit_arg target
    <: Core.explicit_arg motive
    <: Core.explicit_arg cnil
    <: Core.explicit_arg ccons
  in
  (print_string
   @@
   match reducer spine with
   | None -> "None"
   | Some v -> "(Some " ^ Pretty.pp_value Context_view.empty v ^ ")");
  [%expect {| (Some ccons k x xs (Vec/elim A k xs M cnil ccons)) |}]
;;
