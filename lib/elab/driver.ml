module Syntax = Violet_kernel.Syntax
module Level = Violet_kernel.Level
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
  ; bound = Surface.apply_tele (Surface.Var [ name ]) params
  ; implicit = false
  }
;;

let eliminator_motive_type ~name ~params ~deps ~ind_ty =
  let good_deps = rename_tele deps in
  let final_ty = Surface.apply_tele (Surface.Var [ name ]) (params @ good_deps) in
  let final_bind = { name = "_"; bound = final_ty; implicit = false } in
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
  let rec head = function
    | Surface.App (_, f, _) -> head f
    | Surface.Located { value = t; _ } -> head t
    | t -> t
  in
  let patch_delta delta =
    List.concat_map
      (fun bind ->
         if head bind.bound = Surface.Var [ name ]
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
                   (Surface.Var [ "motive" ])
                   (dep_args @ [ Surface.Var [ bind.name ] ])
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
    Surface.apply_tele (Surface.Var [ name; ctor.name ]) (param_args @ renamed_delta)
  in
  { name = "case-" ^ ctor.name
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
      ~deps:[ { name = "_"; bound = Surface.Var [ "Nat" ]; implicit = false } ]
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
      ~deps:[ { name = "_"; bound = Surface.Var [ "Nat" ]; implicit = false } ]
      ~ind_ty:Surface.Universe
      { name = "nil"
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
    { Syntax.name = "case-nil"; bound = ((motive zero) (Vec/nil {A}));
      implicit = false }
    |}]
;;

let%expect_test "Vec case cons" =
  let result =
    eliminator_case
      ~name:"Vec"
      ~params:[ { name = "A"; bound = Surface.Universe; implicit = false } ]
      ~deps:[ { name = "_"; bound = Surface.Var [ "Nat" ]; implicit = false } ]
      ~ind_ty:Surface.Universe
      { name = "cons"
      ; bound =
          Surface.pi
            [ { name = "k"; bound = Surface.Var [ "Nat" ]; implicit = true }
            ; { name = "x"; bound = Surface.Var [ "A" ]; implicit = false }
            ; { name = "xs"
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
    { Syntax.name = "case-cons";
      bound =
      Π{k : Nat} -> Π(x : A) -> Π(xs : ((Vec A) k)) -> Π(ih-xs : ((motive k) xs)) -> ((motive (suc k)) ((((Vec/cons {A}) {k}) x) xs));
      implicit = false }
    |}]
;;

let%expect_test "Vec result type" =
  let result =
    eliminator_result_type
      ~name:"Vec"
      ~params:[ { name = "A"; bound = Surface.Universe; implicit = false } ]
      ~deps:[ { name = "_"; bound = Surface.Var [ "Nat" ]; implicit = false } ]
      ~ind_ty:Surface.Universe
  in
  print_string @@ [%show: Surface.pretype] result;
  [%expect {| ((motive _0) target) |}]
;;

(* These types are defined in Context (elab/context.ml).
   Alias them here so existing code in driver continues to compile unchanged. *)
type binder_kind = Context.binder_kind =
  | Regular
  | Recursive of string list

type ctor_info = Context.ctor_info =
  { ctor_name : string
  ; binder_names : string list
  ; binder_kinds : binder_kind list
  }

type polarity = Context.polarity =
  | StrictlyPositive
  | Unrestricted
[@@deriving show]

type ind_info = Context.ind_info =
  { params : Surface.pretype binder list
  ; deps : Surface.pretype binder list
  ; ind_ty : Surface.pretype
  ; ctors : Surface.pretype binder list
  ; infos : ctor_info list
  ; param_polarity : polarity list
  }

let arities_of (info : ind_info) : (string * int) list =
  List.map (fun ci -> ci.ctor_name, List.length ci.binder_names) info.infos
;;

let rec head_of_surface = function
  | Surface.App (_, f, _) -> head_of_surface f
  | Surface.Located { value = t; _ } -> head_of_surface t
  | t -> t
;;

(* Does the global name `target` occur (as a Surface.Var) anywhere in `t`,
   respecting shadowing by inner binders that re-bind the same name? *)
let occurs_in (target : string) (t : Surface.preterm) : bool =
  let rec go t =
    match t with
    | Surface.Located { value = u; _ } -> go u
    | Surface.Var [ n ] -> String.equal n target
    | Surface.Var _ -> false
    | Surface.App (_, f, x) -> go f || go x
    | Surface.Pi (b, body) -> go b.bound || ((not (String.equal b.name target)) && go body)
    (* Surface.Lambda has no type annotation; `b.bound` is the body. *)
    | Surface.Lambda b -> (not (String.equal b.name target)) && go b.bound
    | Surface.TypedLambda (b, body) ->
      go b.bound || ((not (String.equal b.name target)) && go body)
    | Surface.Max (a, b) -> go a || go b
    | Surface.Universe | Surface.Hole | Surface.Goal _ -> false
  in
  go t
;;

(* Split a term into its head and applied spine (in left-to-right order). *)
let head_and_spine (t : Surface.preterm) : Surface.preterm * Surface.preterm list =
  let rec go t acc =
    match t with
    | Surface.Located { value = u; _ } -> go u acc
    | Surface.App (_, f, x) -> go f (x :: acc)
    | h -> h, acc
  in
  go t []
;;

let%expect_test "occurs_in: Var present" =
  let t = Surface.Var [ "Bad" ] in
  print_string @@ string_of_bool (occurs_in "Bad" t);
  [%expect {| true |}]
;;

let%expect_test "occurs_in: Var absent" =
  let t = Surface.Var [ "Other" ] in
  print_string @@ string_of_bool (occurs_in "Bad" t);
  [%expect {| false |}]
;;

let%expect_test "occurs_in: under App argument" =
  let t = Surface.apply (Surface.Var [ "List" ]) [ Surface.Var [ "Bad" ] ] in
  print_string @@ string_of_bool (occurs_in "Bad" t);
  [%expect {| true |}]
;;

let%expect_test "occurs_in: under Pi domain" =
  let t =
    Surface.Pi
      ( { name = "_"; bound = Surface.Var [ "Bad" ]; implicit = false }
      , Surface.Var [ "X" ] )
  in
  print_string @@ string_of_bool (occurs_in "Bad" t);
  [%expect {| true |}]
;;

let%expect_test "occurs_in: shadowed by inner binder" =
  let t =
    Surface.Pi
      ({ name = "Bad"; bound = Surface.Universe; implicit = false }, Surface.Var [ "Bad" ])
  in
  print_string @@ string_of_bool (occurs_in "Bad" t);
  (* Bad in domain (Universe) doesn't match; in body, Bad is shadowed → no. *)
  [%expect {| false |}]
;;

let%expect_test "occurs_in: Lambda shadows" =
  let t =
    Surface.Lambda { name = "Bad"; bound = Surface.Var [ "Bad" ]; implicit = false }
  in
  print_string @@ string_of_bool (occurs_in "Bad" t);
  (* Body's `Bad` is shadowed by the lambda binder → no. *)
  [%expect {| false |}]
;;

let%expect_test "head_and_spine: bare var" =
  let h, sp = head_and_spine (Surface.Var [ "Nat" ]) in
  Format.printf "%s/%d" ([%show: Surface.preterm] h) (List.length sp);
  [%expect {| Nat/0 |}]
;;

let%expect_test "head_and_spine: applied" =
  let t =
    Surface.apply (Surface.Var [ "Vec" ]) [ Surface.Var [ "A" ]; Surface.Var [ "n" ] ]
  in
  let h, sp = head_and_spine t in
  Format.printf "%s/%d" ([%show: Surface.preterm] h) (List.length sp);
  [%expect {| Vec/2 |}]
;;

let analyze_ctor ~ind_name ~params (ctor : Surface.pretype binder) : ctor_info =
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
  (* Self-reference via let rec: when building the IH for a recursive ctor
     position we need to construct another `Elim` whose head carries this
     very reducer.  Without let rec the IH would be a plain `Var` head with
     no reduction behavior. *)
  let rec reducer (spine : Core.value bwd) : Core.value option =
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
                    [ arg; Core.Elim ({ elim_name; reducer }, ih_spine) ])
               (List.combine own_args info.binder_kinds)
           in
           Some (vapp_list (vapp_list case case_args) trailing))
      | _ -> None)
  in
  reducer
;;

let nat_ctors : Surface.pretype binder list =
  [ { name = "zero"; bound = Surface.Var [ "Nat" ]; implicit = false }
  ; { name = "suc"
    ; bound =
        Surface.Pi
          ( { name = "_"; bound = Surface.Var [ "Nat" ]; implicit = false }
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
  let spine = Emp <: target <: motive <: cz <: cs in
  print_string @@ [%show: Core.value option] (reducer spine);
  [%expect {| (Some cz) |}]
;;

let%expect_test "Nat-elim reduces target=suc n to (case-suc n IH)" =
  let reducer =
    build_elim_reducer ~ind_name:"Nat" ~elim_name:"Nat/elim" ~params:[] ~deps:[] nat_ctors
  in
  let n = Core.Var ("n", Emp) in
  let target = Core.Label ("suc", Emp <: n) in
  let motive = Core.Var ("M", Emp) in
  let cz = Core.Var ("cz", Emp) in
  let cs = Core.Var ("cs", Emp) in
  let spine = Emp <: target <: motive <: cz <: cs in
  print_string @@ [%show: Core.value option] (reducer spine);
  [%expect {| (Some cs n Nat/elim n M cz cs) |}]
;;

let vec_ctors : Surface.pretype binder list =
  [ { name = "nil"
    ; bound =
        Surface.apply
          (Surface.Var [ "Vec" ])
          [ Surface.Var [ "A" ]; Surface.Var [ "zero" ] ]
    ; implicit = false
    }
  ; { name = "cons"
    ; bound =
        Surface.pi
          [ { name = "n"; bound = Surface.Var [ "Nat" ]; implicit = true }
          ; { name = "_"; bound = Surface.Var [ "A" ]; implicit = false }
          ; { name = "_"
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
      ~params:[ { name = "A"; bound = Surface.Universe; implicit = false } ]
      ~deps:[ { name = "_"; bound = Surface.Var [ "Nat" ]; implicit = false } ]
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
  [%expect {| (Some ccons k x xs Vec/elim A k xs M cnil ccons) |}]
;;

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
      ~(lookup_polarity : string -> polarity list option)
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
    match t with
    | Surface.Located { value = u; _ } -> sp ~ctor_name ~arg_ty u
    | Surface.Pi (b, body) ->
      if occurs_in ind_name b.bound then fail_neg ~ctor_name ~arg_ty;
      (* Body keeps the same `arg_ty` for diagnostics. *)
      if not (String.equal b.name ind_name) then sp ~ctor_name ~arg_ty body
    | _ ->
      let h, spine = head_and_spine t in
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
                | Surface.Var [ n ] when String.equal n expected -> ()
                | got -> fail_non_uniform ~ctor_name ~arg_ty ~slot:(i + 1) ~expected ~got
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
                   | StrictlyPositive -> sp ~ctor_name ~arg_ty si
                   | Unrestricted ->
                     if occurs_in ind_name si
                     then fail_foreign ~ctor_name ~arg_ty ~foreign_name:n ~slot:(i + 1)
                   end
                 else if occurs_in ind_name si
                 then fail_foreign ~ctor_name ~arg_ty ~foreign_name:n ~slot:(i + 1))
              spine
          | None -> if occurs_in ind_name t then fail_neg ~ctor_name ~arg_ty)
       | Surface.Var _ ->
         (* Multi-segment path: treat as an unknown external type; if ind_name
            appears anywhere in this subterm then it's a negative occurrence. *)
         if occurs_in ind_name t then fail_neg ~ctor_name ~arg_ty
       | _ -> if occurs_in ind_name t then fail_neg ~ctor_name ~arg_ty)
  in
  List.iter
    (fun (ctor : Surface.pretype binder) ->
       let tele = Surface.telescope ctor.bound in
       List.iter
         (fun (b : Surface.pretype binder) ->
            sp ~ctor_name:ctor.name ~arg_ty:b.bound b.bound)
         tele)
    ctors
;;

let%expect_test "SP: List-shaped clean ctor accepted" =
  (* data List (A : U) | cons : A -> List A -> List A *)
  let cons : Surface.pretype binder =
    { name = "cons"
    ; bound =
        Surface.pi
          [ { name = "_"; bound = Surface.Var [ "A" ]; implicit = false }
          ; { name = "_"
            ; bound = Surface.apply (Surface.Var [ "List" ]) [ Surface.Var [ "A" ] ]
            ; implicit = false
            }
          ]
          (Surface.apply (Surface.Var [ "List" ]) [ Surface.Var [ "A" ] ])
    ; implicit = false
    }
  in
  let params = [ { name = "A"; bound = Surface.Universe; implicit = false } ] in
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
    { name = "b"
    ; bound =
        Surface.pi
          [ { name = "_"
            ; bound =
                Surface.Pi
                  ( { name = "_"; bound = Surface.Var [ "Bad" ]; implicit = false }
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
    { name = "node"
    ; bound =
        Surface.pi
          [ { name = "_"; bound = Surface.Var [ "A" ]; implicit = false }
          ; { name = "_"
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
    if String.equal name "List" then Some [ StrictlyPositive ] else None
  in
  let params = [ { name = "A"; bound = Surface.Universe; implicit = false } ] in
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
    { name = "node"
    ; bound =
        Surface.pi
          [ { name = "_"
            ; bound =
                Surface.apply
                  (Surface.Var [ "Tree" ])
                  [ Surface.Pi
                      ( { name = "_"; bound = Surface.Var [ "A" ]; implicit = false }
                      , Surface.Var [ "A" ] )
                  ]
            ; implicit = false
            }
          ]
          (Surface.apply (Surface.Var [ "Tree" ]) [ Surface.Var [ "A" ] ])
    ; implicit = false
    }
  in
  let params = [ { name = "A"; bound = Surface.Universe; implicit = false } ] in
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
    { name = "bad"
    ; bound =
        Surface.pi
          [ { name = "_"
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
  let params = [ { name = "A"; bound = Surface.Universe; implicit = false } ] in
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
      ~(lookup_polarity : string -> polarity list option)
      (ctors : Surface.pretype binder list)
  : polarity list
  =
  let param_names = List.map (fun (p : Surface.pretype binder) -> p.name) params in
  let demoted = ref [] in
  let is_demoted name = List.exists (String.equal name) !demoted in
  let demote name = if not (is_demoted name) then demoted := name :: !demoted in
  let demote_if_in term =
    List.iter
      (fun pn -> if (not (is_demoted pn)) && occurs_in pn term then demote pn)
      param_names
  in
  let rec walk t =
    match t with
    | Surface.Located { value = u; _ } -> walk u
    | Surface.Pi (b, body) ->
      (* Any param occurrence inside b.bound is contravariant → demote. *)
      demote_if_in b.bound;
      (* Body: continue walking (binder may shadow but param names are
         top-level; shadowing inside a ctor binder is unusual and the
         occurs_in itself respects shadowing for that subterm). *)
      if not (List.exists (String.equal b.name) param_names) then walk body
    | _ ->
      let h, spine = head_and_spine t in
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
                   | StrictlyPositive -> walk si
                   | Unrestricted -> demote_if_in si
                   end
                 else demote_if_in si)
              spine
          | None ->
            (* Unknown head (local, unresolved): any param occurrence demotes. *)
            demote_if_in t)
       | Surface.Var _ ->
         (* Multi-segment qualified name: treat as unknown external; demote if
            any param appears in the whole subterm. *)
         demote_if_in t
       | _ -> demote_if_in t)
  in
  List.iter
    (fun (ctor : Surface.pretype binder) ->
       let tele = Surface.telescope ctor.bound in
       List.iter (fun (b : Surface.pretype binder) -> walk b.bound) tele)
    ctors;
  List.map
    (fun pn -> if is_demoted pn then Unrestricted else StrictlyPositive)
    param_names
;;

let%expect_test "polarity: List has all SP params" =
  let cons : Surface.pretype binder =
    { name = "cons"
    ; bound =
        Surface.pi
          [ { name = "_"; bound = Surface.Var [ "A" ]; implicit = false }
          ; { name = "_"
            ; bound = Surface.apply (Surface.Var [ "List" ]) [ Surface.Var [ "A" ] ]
            ; implicit = false
            }
          ]
          (Surface.apply (Surface.Var [ "List" ]) [ Surface.Var [ "A" ] ])
    ; implicit = false
    }
  in
  let params = [ { name = "A"; bound = Surface.Universe; implicit = false } ] in
  let pol =
    infer_param_polarity
      ~ind_name:"List"
      ~params
      ~lookup_polarity:(fun _ -> None)
      [ cons ]
  in
  print_string @@ [%show: polarity list] pol;
  [%expect {| [Context.StrictlyPositive] |}]
;;

let%expect_test "polarity: param negative under Pi demoted" =
  (* data D (A : U) | mk : (A -> Bool) -> D A *)
  let mk : Surface.pretype binder =
    { name = "mk"
    ; bound =
        Surface.pi
          [ { name = "_"
            ; bound =
                Surface.Pi
                  ( { name = "_"; bound = Surface.Var [ "A" ]; implicit = false }
                  , Surface.Var [ "Bool" ] )
            ; implicit = false
            }
          ]
          (Surface.apply (Surface.Var [ "D" ]) [ Surface.Var [ "A" ] ])
    ; implicit = false
    }
  in
  let params = [ { name = "A"; bound = Surface.Universe; implicit = false } ] in
  let pol =
    infer_param_polarity ~ind_name:"D" ~params ~lookup_polarity:(fun _ -> None) [ mk ]
  in
  print_string @@ [%show: polarity list] pol;
  [%expect {| [Context.Unrestricted] |}]
;;

let%expect_test "polarity: Rose nested under List positive slot stays SP" =
  let node : Surface.pretype binder =
    { name = "node"
    ; bound =
        Surface.pi
          [ { name = "_"; bound = Surface.Var [ "A" ]; implicit = false }
          ; { name = "_"
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
    if String.equal name "List" then Some [ StrictlyPositive ] else None
  in
  let params = [ { name = "A"; bound = Surface.Universe; implicit = false } ] in
  let pol =
    infer_param_polarity ~ind_name:"Rose" ~params ~lookup_polarity:lookup [ node ]
  in
  print_string @@ [%show: polarity list] pol;
  [%expect {| [Context.StrictlyPositive] |}]
;;
