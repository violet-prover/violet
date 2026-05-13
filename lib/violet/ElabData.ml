open Syntax

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
