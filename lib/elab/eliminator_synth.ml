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

(* Synthesized Surface nodes inherit the location of the originating data
   declaration (threaded as [~loc], the declaration's [ind_ty.loc]). *)
let at loc node : Surface.preterm = Surface.Mk.at loc node
let sn loc value : binder_name Surface.spanned = { Surface.loc; value }

(* Give anonymous binders unique names so they can be referenced later
   (e.g. as constructor arguments in the eliminator's spine). Leave named
   binders alone — renaming them would invalidate downstream references to
   the original name (the references aren't rewritten). *)
let rename_tele tele : Surface.pretype Surface.sbinder list =
  List.mapi
    (fun i (bind : Surface.pretype Surface.sbinder) ->
       match bind.name.Surface.value with
       | Anon ->
         { bind with
           name = { bind.name with Surface.value = Named (Printf.sprintf "_%d" i) }
         }
       | Named _ -> bind)
    tele
;;

let eliminator_params ~name ~params ~deps ~ind_ty =
  let _ = name in
  let _ = ind_ty in
  let good_deps = rename_tele deps in
  params @ good_deps
;;

let eliminator_target_binding ~loc ~name ~params ~deps ~ind_ty =
  let params = eliminator_params ~name ~params ~deps ~ind_ty in
  { Surface.name = sn loc (Named "target")
  ; bound = Surface.apply_tele (at loc (Surface.Var [ name ])) params
  ; implicit = false
  }
;;

let eliminator_motive_type ~loc ~name ~params ~deps ~ind_ty =
  let good_deps = rename_tele deps in
  let final_ty = Surface.apply_tele (at loc (Surface.Var [ name ])) (params @ good_deps) in
  let final_bind = { Surface.name = sn loc Anon; bound = final_ty; implicit = false } in
  Surface.pi (good_deps @ [ final_bind ]) ind_ty
;;

let eliminator_result_type ~loc ~name ~params ~deps ~ind_ty =
  let _ = name in
  let _ = params in
  let _ = ind_ty in
  let good_deps = rename_tele deps in
  let t = Surface.apply_tele (at loc (Surface.Var [ "motive" ])) good_deps in
  Surface.apply t [ at loc (Surface.Var [ "target" ]) ]
;;

let eliminator_case ~loc ~name ~params ~deps ~ind_ty (ctor : Surface.pretype Surface.sbinder)
  : Surface.pretype Surface.sbinder
  =
  let _ = deps in
  let _ = ind_ty in
  let patch_delta delta =
    List.concat_map
      (fun (bind : Surface.pretype Surface.sbinder) ->
         if (head_of_surface bind.bound).Surface.node = Surface.Var [ name ]
         then (
           (* Motive takes (deps ... , target), so the IH must mirror that
              shape — supply the recursive point's dep arguments, not just
              the point itself. *)
           let rec_spine = Surface.applied_spine bind.bound in
           let dep_args = List.drop (List.length params) rec_spine in
           [ bind
           ; { Surface.name = sn loc (Named ("ih-" ^ Name.to_string bind.name.Surface.value))
             ; bound =
                 Surface.apply
                   (at loc (Surface.Var [ "motive" ]))
                   (dep_args
                    @ [ at loc (Surface.Var [ Name.to_string bind.name.Surface.value ]) ])
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
  let n_explicit_params =
    List.length
      (List.filter (fun (p : Surface.pretype Surface.sbinder) -> not p.implicit) params)
  in
  let spine = List.drop n_explicit_params spine in
  (* The constructor's stored type is wrapped with implicit data params by
     `close_ctor_type`, so applying it requires those params up front. They
     resolve to the eliminator's outer params (which are in scope here). *)
  let param_args =
    List.map
      (fun (p : Surface.pretype Surface.sbinder) -> { p with Surface.implicit = true })
      params
  in
  let final =
    Surface.apply_tele
      (at loc (Surface.Var [ name; Name.to_string ctor.name.Surface.value ]))
      (param_args @ renamed_delta)
  in
  { Surface.name = sn loc (Named ("case-" ^ Name.to_string ctor.name.Surface.value))
  ; bound =
      Surface.pi
        (patch_delta renamed_delta)
        (Surface.apply (at loc (Surface.Var [ "motive" ])) (spine @ [ final ]))
  ; implicit = false
  }
;;

let eliminator_type ~loc ~name ~params ~deps ~ind_ty ctors =
  let elim_params = eliminator_params ~name ~params ~deps ~ind_ty in
  let target_bind = eliminator_target_binding ~loc ~name ~params ~deps ~ind_ty in
  let motive_type = eliminator_motive_type ~loc ~name ~params ~deps ~ind_ty in
  let case_binds =
    List.map (fun c -> eliminator_case ~loc ~name ~params ~deps ~ind_ty c) ctors
  in
  let result_ty = eliminator_result_type ~loc ~name ~params ~deps ~ind_ty in
  Surface.pi
    (elim_params
     @ [ target_bind
       ; { Surface.name = sn loc (Named "motive"); bound = motive_type; implicit = false }
       ]
     @ case_binds)
    result_ty
;;

let dloc = Surface.dummy_loc
let d node = Surface.Mk.at dloc node
let dn value : binder_name Surface.spanned = { Surface.loc = dloc; value }

let%expect_test "`data List (A : U) : U`, the generated eliminator will rely on A" =
  let result =
    eliminator_params
      ~name:"List"
      ~params:[ { Surface.name = dn (Named "A"); bound = d Surface.Universe; implicit = false } ]
      ~deps:[]
      ~ind_ty:(d Surface.Universe)
  in
  print_string @@ [%show: Surface.pretype Surface.sbinder list] result;
  [%expect {|
    [{ Surface.name = (Violet_kernel.Syntax.Named "A"); bound = 𝓤;
       implicit = false }
      ]
    |}]
;;

let%expect_test "List target has type `List A`" =
  let result =
    eliminator_target_binding
      ~loc:dloc
      ~name:"List"
      ~params:[ { Surface.name = dn (Named "A"); bound = d Surface.Universe; implicit = false } ]
      ~deps:[]
      ~ind_ty:(d Surface.Universe)
  in
  print_string @@ [%show: Surface.pretype Surface.sbinder] result;
  [%expect
    {|
    { Surface.name = (Violet_kernel.Syntax.Named "target"); bound = (List A);
      implicit = false }
    |}]
;;

let%expect_test "Vec motive" =
  let result =
    eliminator_motive_type
      ~loc:dloc
      ~name:"Vec"
      ~params:[ { Surface.name = dn (Named "A"); bound = d Surface.Universe; implicit = false } ]
      ~deps:[ { Surface.name = dn Anon; bound = d (Surface.Var [ "Nat" ]); implicit = false } ]
      ~ind_ty:(d Surface.Universe)
  in
  print_string @@ [%show: Surface.pretype] result;
  [%expect {| Π(_0 : Nat) -> Π(_ : ((Vec A) _0)) -> 𝓤 |}]
;;

let%expect_test "Vec case nil" =
  let result =
    eliminator_case
      ~loc:dloc
      ~name:"Vec"
      ~params:[ { Surface.name = dn (Named "A"); bound = d Surface.Universe; implicit = false } ]
      ~deps:[ { Surface.name = dn Anon; bound = d (Surface.Var [ "Nat" ]); implicit = false } ]
      ~ind_ty:(d Surface.Universe)
      { Surface.name = dn (Named "nil")
      ; bound =
          Surface.apply
            (d (Surface.Var [ "Vec" ]))
            [ d (Surface.Var [ "A" ]); d (Surface.Var [ "zero" ]) ]
      ; implicit = false
      }
  in
  print_string @@ [%show: Surface.pretype Surface.sbinder] result;
  [%expect
    {|
    { Surface.name = (Violet_kernel.Syntax.Named "case-nil");
      bound = ((motive zero) (Vec/nil {A})); implicit = false }
    |}]
;;

let%expect_test "Vec case cons" =
  let result =
    eliminator_case
      ~loc:dloc
      ~name:"Vec"
      ~params:[ { Surface.name = dn (Named "A"); bound = d Surface.Universe; implicit = false } ]
      ~deps:[ { Surface.name = dn Anon; bound = d (Surface.Var [ "Nat" ]); implicit = false } ]
      ~ind_ty:(d Surface.Universe)
      { Surface.name = dn (Named "cons")
      ; bound =
          Surface.pi
            [ { Surface.name = dn (Named "k"); bound = d (Surface.Var [ "Nat" ]); implicit = true }
            ; { Surface.name = dn (Named "x"); bound = d (Surface.Var [ "A" ]); implicit = false }
            ; { Surface.name = dn (Named "xs")
              ; bound =
                  Surface.apply
                    (d (Surface.Var [ "Vec" ]))
                    [ d (Surface.Var [ "A" ]); d (Surface.Var [ "k" ]) ]
              ; implicit = false
              }
            ]
            (Surface.apply
               (d (Surface.Var [ "Vec" ]))
               [ d (Surface.Var [ "A" ])
               ; Surface.apply (d (Surface.Var [ "suc" ])) [ d (Surface.Var [ "k" ]) ]
               ])
      ; implicit = false
      }
  in
  print_string @@ [%show: Surface.pretype Surface.sbinder] result;
  [%expect
    {|
    { Surface.name = (Violet_kernel.Syntax.Named "case-cons");
      bound =
      Π{k : Nat} -> Π(x : A) -> Π(xs : ((Vec A) k)) -> Π(ih-xs : ((motive k) xs)) -> ((motive (suc k)) ((((Vec/cons {A}) {k}) x) xs));
      implicit = false }
    |}]
;;

let%expect_test "Vec result type" =
  let result =
    eliminator_result_type
      ~loc:dloc
      ~name:"Vec"
      ~params:[ { Surface.name = dn (Named "A"); bound = d Surface.Universe; implicit = false } ]
      ~deps:[ { Surface.name = dn Anon; bound = d (Surface.Var [ "Nat" ]); implicit = false } ]
      ~ind_ty:(d Surface.Universe)
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
      (c : Surface.pretype Surface.sbinder)
  : string list * string list
  =
  let delta = rename_tele (Surface.telescope c.bound) in
  let lambdas = ref [] in
  let fields = ref [] in
  List.iter
    (fun (b : Surface.pretype Surface.sbinder) ->
       let n = prefix ^ Name.to_string b.name.Surface.value in
       fields := n :: !fields;
       lambdas := n :: !lambdas;
       if (head_of_surface b.bound).Surface.node = Surface.Var [ ind_name ]
       then lambdas := (prefix ^ "ih-" ^ Name.to_string b.name.Surface.value) :: !lambdas)
    delta;
  List.rev !lambdas, List.rev !fields
;;

let analyze_ctor ~ind_name ~params (ctor : Surface.pretype Surface.sbinder)
  : Context.ctor_info
  =
  let delta = rename_tele (Surface.telescope ctor.bound) in
  let n_explicit_params =
    List.length
      (List.filter (fun (p : Surface.pretype Surface.sbinder) -> not p.implicit) params)
  in
  let kinds =
    List.map
      (fun (b : Surface.pretype Surface.sbinder) ->
         if (head_of_surface b.bound).Surface.node = Surface.Var [ ind_name ]
         then (
           let rec_spine = Surface.applied_spine b.bound in
           let dep_args = List.drop n_explicit_params rec_spine in
           let dep_names =
             List.map
               (fun (a : Surface.preterm) ->
                  match a.Surface.node with
                  | Surface.Var [ n ] -> n
                  | _ -> "_")
               dep_args
           in
           Context.Recursive dep_names)
         else Context.Regular)
      delta
  in
  { ctor_name = Name.to_string ctor.name.Surface.value
  ; binder_names =
      List.map
        (fun (b : Surface.pretype Surface.sbinder) -> Name.to_string b.name.Surface.value)
        delta
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
      ~(params : Surface.pretype Surface.sbinder list)
      ~(deps : Surface.pretype Surface.sbinder list)
      (ctors : Surface.pretype Surface.sbinder list)
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

let nat_ctors : Surface.pretype Surface.sbinder list =
  [ { Surface.name = dn (Named "zero"); bound = d (Surface.Var [ "Nat" ]); implicit = false }
  ; { Surface.name = dn (Named "suc")
    ; bound =
        d (Surface.Pi
             ( { Surface.name = dn Anon
               ; bound = d (Surface.Var [ "Nat" ])
               ; implicit = false
               }
             , d (Surface.Var [ "Nat" ]) ))
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

let vec_ctors : Surface.pretype Surface.sbinder list =
  [ { Surface.name = dn (Named "nil")
    ; bound =
        Surface.apply
          (d (Surface.Var [ "Vec" ]))
          [ d (Surface.Var [ "A" ]); d (Surface.Var [ "zero" ]) ]
    ; implicit = false
    }
  ; { Surface.name = dn (Named "cons")
    ; bound =
        Surface.pi
          [ { Surface.name = dn (Named "n"); bound = d (Surface.Var [ "Nat" ]); implicit = true }
          ; { Surface.name = dn Anon; bound = d (Surface.Var [ "A" ]); implicit = false }
          ; { Surface.name = dn Anon
            ; bound =
                Surface.apply
                  (d (Surface.Var [ "Vec" ]))
                  [ d (Surface.Var [ "A" ]); d (Surface.Var [ "n" ]) ]
            ; implicit = false
            }
          ]
          (Surface.apply
             (d (Surface.Var [ "Vec" ]))
             [ d (Surface.Var [ "A" ])
             ; Surface.apply (d (Surface.Var [ "suc" ])) [ d (Surface.Var [ "n" ]) ]
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
      ~params:[ { Surface.name = dn (Named "A"); bound = d Surface.Universe; implicit = false } ]
      ~deps:[ { Surface.name = dn Anon; bound = d (Surface.Var [ "Nat" ]); implicit = false } ]
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
