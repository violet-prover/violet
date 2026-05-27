open Violet_surface
open Violet_common
module Syntax = Violet_kernel.Syntax
open Syntax
open Surface_utils

(* Strict positivity check for a single inductive declaration.
   `ind_name`  — name of the inductive being defined.
   `params`    — declared parameters; their names anchor the uniformity test.
   `deps`      — declared dependencies (indices). Carried for arity arithmetic.
   `lookup_polarity` — returns `Some pols` if a name resolves to a previously
                       declared inductive (with one entry per declared param),
                       or `None` otherwise (locals, non-inductive globals).
   `ctors`     — list of constructor binders to check.

   Raises via `Reporter.fatalf ~loc Type_error` on the first violation. *)
let check_strict_positivity
      ~(loc : Asai.Range.t option)
      ~(ind_name : string)
      ~(params : Surface.pretype binder list)
      ~(deps : Surface.pretype binder list)
      ~(lookup_polarity : string -> Context.polarity list option)
      (ctors : Surface.pretype binder list)
  : unit
  =
  (* deps names are not needed here; n_params suffices to split param-
     vs index-slot positions in the spine when checking recursive uses. *)
  let _ = deps in
  let n_params = List.length params in
  let param_names = List.map (fun (p : Surface.pretype binder) -> p.name) params in
  let fail_neg ~ctor_name ~arg_ty =
    Reporter.fatalf
      ?loc
      Type_error
      "constructor `%s` of `%s` places `%s` in a negative position:\n\
      \  in argument type `%s`,\n\
      \  `%s` occurs to the left of `->`."
      ctor_name
      ind_name
      ind_name
      ([%show: Surface.preterm] arg_ty)
      ind_name
  in
  let fail_foreign ~ctor_name ~arg_ty ~foreign_name ~slot =
    Reporter.fatalf
      ?loc
      Type_error
      "constructor `%s` of `%s` places `%s` under non-positive slot of `%s`:\n\
      \  in argument type `%s`,\n\
      \  parameter %d of `%s` is not strictly positive."
      ctor_name
      ind_name
      ind_name
      foreign_name
      ([%show: Surface.preterm] arg_ty)
      slot
      foreign_name
  in
  let fail_non_uniform ~ctor_name ~arg_ty ~slot ~expected ~got =
    Reporter.fatalf
      ?loc
      Type_error
      "constructor `%s` of `%s` uses `%s` non-uniformly:\n\
      \  in argument type `%s`,\n\
      \  parameter %d must be `%s` (the declared param) but is `%s`."
      ctor_name
      ind_name
      ind_name
      ([%show: Surface.preterm] arg_ty)
      slot
      expected
      ([%show: Surface.preterm] got)
  in
  let rec sp ~ctor_name ~arg_ty t =
    let binders, cod = linearize_pi t in
    (* Check each Pi-domain for negative occurrences of `ind_name`; stop the
       chain as soon as a binder shadows `ind_name` (its body is then
       unreachable from the perspective of the strict-positivity check). *)
    let rec scan_binders = function
      | [] -> Some cod
      | (b : Surface.pretype binder) :: rest ->
        if occurs_in ind_name b.bound then fail_neg ~ctor_name ~arg_ty;
        if b.name = Named ind_name then None else scan_binders rest
    in
    match scan_binders binders with
    | None -> ()
    | Some cod ->
      let h, spine = head_and_spine cod in
      (match h with
       | Surface.Var [ n ] when String.equal n ind_name ->
         (* Recursive self-use. Param slots must match the declared param
            names (uniform recursion); index slots are values that must
            not mention the inductive being defined. *)
         let rec strip = function
           | Surface.Located { value = u; _ } -> strip u
           | other -> other
         in
         List.iteri
           (fun i si ->
              if i < n_params
              then begin
                let expected = List.nth param_names i in
                match strip si with
                | Surface.Var [ n ] when Named n = expected -> ()
                | got ->
                  fail_non_uniform
                    ~ctor_name
                    ~arg_ty
                    ~slot:(i + 1)
                    ~expected:(Name.to_string expected)
                    ~got
              end
              else if occurs_in ind_name si
              then fail_neg ~ctor_name ~arg_ty)
           spine
       | Surface.Var [ n ] ->
         (match lookup_polarity n with
          | Some pols ->
            let n_pols = List.length pols in
            List.iteri
              (fun i si ->
                 if i < n_pols
                 then
                   begin match List.nth pols i with
                   | Context.StrictlyPositive -> sp ~ctor_name ~arg_ty si
                   | Context.Unrestricted ->
                     if occurs_in ind_name si
                     then fail_foreign ~ctor_name ~arg_ty ~foreign_name:n ~slot:(i + 1)
                   end
                 else if occurs_in ind_name si
                 then fail_foreign ~ctor_name ~arg_ty ~foreign_name:n ~slot:(i + 1))
              spine
          | None -> if occurs_in ind_name cod then fail_neg ~ctor_name ~arg_ty)
       | Surface.Var _ ->
         (* Multi-segment path: treat as an unknown external type; if ind_name
            appears anywhere in this subterm then it's a negative occurrence. *)
         if occurs_in ind_name cod then fail_neg ~ctor_name ~arg_ty
       | _ -> if occurs_in ind_name cod then fail_neg ~ctor_name ~arg_ty)
  in
  List.iter
    (fun (ctor : Surface.pretype binder) ->
       let tele = Surface.telescope ctor.bound in
       List.iter
         (fun (b : Surface.pretype binder) ->
            sp ~ctor_name:(Name.to_string ctor.name) ~arg_ty:b.bound b.bound)
         tele)
    ctors
;;

let%expect_test "SP: List-shaped clean ctor accepted" =
  (* data List (A : U) | cons : A -> List A -> List A *)
  let cons : Surface.pretype binder =
    { name = Named "cons"
    ; bound =
        Surface.pi
          [ { name = Anon; bound = Surface.Var [ "A" ]; implicit = false }
          ; { name = Anon
            ; bound = Surface.apply (Surface.Var [ "List" ]) [ Surface.Var [ "A" ] ]
            ; implicit = false
            }
          ]
          (Surface.apply (Surface.Var [ "List" ]) [ Surface.Var [ "A" ] ])
    ; implicit = false
    }
  in
  let params = [ { name = Named "A"; bound = Surface.Universe; implicit = false } ] in
  let result =
    Reporter.run
      ~emit:(fun _ -> ())
      ~fatal:(fun _ -> "rejected")
      (fun () ->
         check_strict_positivity
           ~loc:None
           ~ind_name:"List"
           ~params
           ~deps:[]
           ~lookup_polarity:(fun _ -> None)
           [ cons ];
         "ok")
  in
  print_string result;
  [%expect {| ok |}]
;;

let%expect_test "SP: negative occurrence rejected" =
  (* data Bad | b : (Bad -> Bad) -> Bad *)
  let b : Surface.pretype binder =
    { name = Named "b"
    ; bound =
        Surface.pi
          [ { name = Anon
            ; bound =
                Surface.Pi
                  ( { name = Anon; bound = Surface.Var [ "Bad" ]; implicit = false }
                  , Surface.Var [ "Bad" ] )
            ; implicit = false
            }
          ]
          (Surface.Var [ "Bad" ])
    ; implicit = false
    }
  in
  let result =
    Reporter.run
      ~emit:(fun _ -> ())
      ~fatal:(fun _ -> "rejected")
      (fun () ->
         check_strict_positivity
           ~loc:None
           ~ind_name:"Bad"
           ~params:[]
           ~deps:[]
           ~lookup_polarity:(fun _ -> None)
           [ b ];
         "ok")
  in
  print_string result;
  [%expect {| rejected |}]
;;

let%expect_test "SP: nested under List positive slot accepted" =
  (* data Rose (A : U) | node : A -> List (Rose A) -> Rose A
     Assume List has param_polarity = [StrictlyPositive]. *)
  let node : Surface.pretype binder =
    { name = Named "node"
    ; bound =
        Surface.pi
          [ { name = Anon; bound = Surface.Var [ "A" ]; implicit = false }
          ; { name = Anon
            ; bound =
                Surface.apply
                  (Surface.Var [ "List" ])
                  [ Surface.apply (Surface.Var [ "Rose" ]) [ Surface.Var [ "A" ] ] ]
            ; implicit = false
            }
          ]
          (Surface.apply (Surface.Var [ "Rose" ]) [ Surface.Var [ "A" ] ])
    ; implicit = false
    }
  in
  let lookup name =
    if String.equal name "List" then Some [ Context.StrictlyPositive ] else None
  in
  let params = [ { name = Named "A"; bound = Surface.Universe; implicit = false } ] in
  let result =
    Reporter.run
      ~emit:(fun _ -> ())
      ~fatal:(fun _ -> "rejected")
      (fun () ->
         check_strict_positivity
           ~loc:None
           ~ind_name:"Rose"
           ~params
           ~deps:[]
           ~lookup_polarity:lookup
           [ node ];
         "ok")
  in
  print_string result;
  [%expect {| ok |}]
;;

let%expect_test "SP: non-uniform recursive use rejected" =
  (* data Tree (A : U) | node : Tree (A -> A) -> Tree A *)
  let node : Surface.pretype binder =
    { name = Named "node"
    ; bound =
        Surface.pi
          [ { name = Anon
            ; bound =
                Surface.apply
                  (Surface.Var [ "Tree" ])
                  [ Surface.Pi
                      ( { name = Anon; bound = Surface.Var [ "A" ]; implicit = false }
                      , Surface.Var [ "A" ] )
                  ]
            ; implicit = false
            }
          ]
          (Surface.apply (Surface.Var [ "Tree" ]) [ Surface.Var [ "A" ] ])
    ; implicit = false
    }
  in
  let params = [ { name = Named "A"; bound = Surface.Universe; implicit = false } ] in
  let result =
    Reporter.run
      ~emit:(fun _ -> ())
      ~fatal:(fun _ -> "rejected")
      (fun () ->
         check_strict_positivity
           ~loc:None
           ~ind_name:"Tree"
           ~params
           ~deps:[]
           ~lookup_polarity:(fun _ -> None)
           [ node ];
         "ok")
  in
  print_string result;
  [%expect {| rejected |}]
;;

let%expect_test "SP: non-uniform nested self-use produces non-uniform error" =
  (* data Tree (A : U) | bad : Tree (Tree A) -> Tree A *)
  let bad : Surface.pretype binder =
    { name = Named "bad"
    ; bound =
        Surface.pi
          [ { name = Anon
            ; bound =
                Surface.apply
                  (Surface.Var [ "Tree" ])
                  [ Surface.apply (Surface.Var [ "Tree" ]) [ Surface.Var [ "A" ] ] ]
            ; implicit = false
            }
          ]
          (Surface.apply (Surface.Var [ "Tree" ]) [ Surface.Var [ "A" ] ])
    ; implicit = false
    }
  in
  let params = [ { name = Named "A"; bound = Surface.Universe; implicit = false } ] in
  let result =
    Reporter.run
      ~emit:(fun _ -> ())
      ~fatal:(fun _ -> "rejected")
      (fun () ->
         check_strict_positivity
           ~loc:None
           ~ind_name:"Tree"
           ~params
           ~deps:[]
           ~lookup_polarity:(fun _ -> None)
           [ bad ];
         "ok")
  in
  print_string result;
  [%expect {| rejected |}]
;;

(* For each declared param P_i, scan all ctor-arg types and decide whether
   any occurrence of P_i forces demotion to Unrestricted. Recursive uses of
   the inductive being defined are skipped (uniformity, enforced by
   check_strict_positivity, guarantees P_i only appears in its own slot). *)
let infer_param_polarity
      ~(ind_name : string)
      ~(params : Surface.pretype binder list)
      ~(lookup_polarity : string -> Context.polarity list option)
      (ctors : Surface.pretype binder list)
  : Context.polarity list
  =
  let param_names =
    List.map (fun (p : Surface.pretype binder) -> Name.to_string p.name) params
  in
  let demoted = ref [] in
  let is_demoted name = List.exists (String.equal name) !demoted in
  let demote name = if not (is_demoted name) then demoted := name :: !demoted in
  let demote_if_in term =
    List.iter
      (fun pn -> if (not (is_demoted pn)) && occurs_in pn term then demote pn)
      param_names
  in
  let rec walk t =
    let binders, cod = linearize_pi t in
    (* Each Pi-domain is a contravariant position for any param that occurs
       in it → demote. A binder that shadows a param stops the chain. *)
    let rec scan_binders = function
      | [] -> Some cod
      | (b : Surface.pretype binder) :: rest ->
        demote_if_in b.bound;
        if List.exists (String.equal (Name.to_string b.name)) param_names
        then None
        else scan_binders rest
    in
    match scan_binders binders with
    | None -> ()
    | Some cod ->
      let h, spine = head_and_spine cod in
      (match h with
       | Surface.Var [ n ] when String.equal n ind_name ->
         (* Skip self-use; uniformity makes it a pure propagation. *)
         ()
       | Surface.Var [ n ] when List.exists (String.equal n) param_names ->
         (* Head is a param used directly as a type (e.g. `A` as an arg type).
            This is a positive occurrence — do nothing. *)
         ()
       | Surface.Var [ n ] ->
         (match lookup_polarity n with
          | Some pols ->
            let n_pols = List.length pols in
            List.iteri
              (fun i si ->
                 if i < n_pols
                 then
                   begin match List.nth pols i with
                   | Context.StrictlyPositive -> walk si
                   | Context.Unrestricted -> demote_if_in si
                   end
                 else demote_if_in si)
              spine
          | None ->
            (* Unknown head (local, unresolved): any param occurrence demotes. *)
            demote_if_in cod)
       | Surface.Var _ ->
         (* Multi-segment qualified name: treat as unknown external; demote if
            any param appears in the whole subterm. *)
         demote_if_in cod
       | _ -> demote_if_in cod)
  in
  List.iter
    (fun (ctor : Surface.pretype binder) ->
       let tele = Surface.telescope ctor.bound in
       List.iter (fun (b : Surface.pretype binder) -> walk b.bound) tele)
    ctors;
  List.map
    (fun pn -> if is_demoted pn then Context.Unrestricted else Context.StrictlyPositive)
    param_names
;;

let%expect_test "polarity: List has all SP params" =
  let cons : Surface.pretype binder =
    { name = Named "cons"
    ; bound =
        Surface.pi
          [ { name = Anon; bound = Surface.Var [ "A" ]; implicit = false }
          ; { name = Anon
            ; bound = Surface.apply (Surface.Var [ "List" ]) [ Surface.Var [ "A" ] ]
            ; implicit = false
            }
          ]
          (Surface.apply (Surface.Var [ "List" ]) [ Surface.Var [ "A" ] ])
    ; implicit = false
    }
  in
  let params = [ { name = Named "A"; bound = Surface.Universe; implicit = false } ] in
  let pol =
    infer_param_polarity
      ~ind_name:"List"
      ~params
      ~lookup_polarity:(fun _ -> None)
      [ cons ]
  in
  print_string @@ [%show: Context.polarity list] pol;
  [%expect {| [Context.StrictlyPositive] |}]
;;

let%expect_test "polarity: param negative under Pi demoted" =
  (* data D (A : U) | mk : (A -> Bool) -> D A *)
  let mk : Surface.pretype binder =
    { name = Named "mk"
    ; bound =
        Surface.pi
          [ { name = Anon
            ; bound =
                Surface.Pi
                  ( { name = Anon; bound = Surface.Var [ "A" ]; implicit = false }
                  , Surface.Var [ "Bool" ] )
            ; implicit = false
            }
          ]
          (Surface.apply (Surface.Var [ "D" ]) [ Surface.Var [ "A" ] ])
    ; implicit = false
    }
  in
  let params = [ { name = Named "A"; bound = Surface.Universe; implicit = false } ] in
  let pol =
    infer_param_polarity ~ind_name:"D" ~params ~lookup_polarity:(fun _ -> None) [ mk ]
  in
  print_string @@ [%show: Context.polarity list] pol;
  [%expect {| [Context.Unrestricted] |}]
;;

let%expect_test "polarity: Rose nested under List positive slot stays SP" =
  let node : Surface.pretype binder =
    { name = Named "node"
    ; bound =
        Surface.pi
          [ { name = Anon; bound = Surface.Var [ "A" ]; implicit = false }
          ; { name = Anon
            ; bound =
                Surface.apply
                  (Surface.Var [ "List" ])
                  [ Surface.apply (Surface.Var [ "Rose" ]) [ Surface.Var [ "A" ] ] ]
            ; implicit = false
            }
          ]
          (Surface.apply (Surface.Var [ "Rose" ]) [ Surface.Var [ "A" ] ])
    ; implicit = false
    }
  in
  let lookup name =
    if String.equal name "List" then Some [ Context.StrictlyPositive ] else None
  in
  let params = [ { name = Named "A"; bound = Surface.Universe; implicit = false } ] in
  let pol =
    infer_param_polarity ~ind_name:"Rose" ~params ~lookup_polarity:lookup [ node ]
  in
  print_string @@ [%show: Context.polarity list] pol;
  [%expect {| [Context.StrictlyPositive] |}]
;;
