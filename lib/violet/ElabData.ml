open Syntax

let rename_tele tele : Surface.pretype binder list =
  List.mapi (fun i bind -> { bind with name = bind.name ^ string_of_int i }) tele
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
         then
           [ bind
           ; { name = "ih-" ^ bind.name
             ; bound = Surface.apply (Surface.Var "motive") [ Surface.Var bind.name ]
             ; implicit = false
             }
           ]
         else [ bind ])
      delta
  in
  let delta = Surface.telescope ctor.bound in
  let spine = Surface.applied_spine (Surface.codomain ctor.bound) in
  let spine = List.drop (List.length params) spine in
  let final = Surface.apply_tele (Surface.Var ctor.name) delta in
  { name = "case-" ^ ctor.name
  ; bound =
      Surface.pi
        (patch_delta (rename_tele delta))
        (Surface.apply (Surface.Var "motive") (spine @ [ final ]))
  ; implicit = false
  }
;;

let eliminator_type ~name ~params ~deps ~ind_ty ctors =
  let params = eliminator_params ~name ~params ~deps ~ind_ty in
  let target_bind = eliminator_target_binding ~name ~params ~deps ~ind_ty in
  let motive_type = eliminator_motive_type ~name ~params ~deps ~ind_ty in
  let case_binds =
    List.map (fun c -> eliminator_case ~name ~params ~deps ~ind_ty c) ctors
  in
  let result_ty = eliminator_result_type ~name ~params ~deps ~ind_ty in
  Surface.pi
    (params
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
    {| { Syntax.name = "case-nil"; bound = ((motive zero) nil); implicit = false } |}]
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
      Π{k0 : Nat} -> Π(x1 : A) -> Π(xs2 : ((Vec A) k)) -> Π(ih-xs2 : (motive xs2)) -> ((motive (suc k)) (((cons {k}) x) xs));
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
