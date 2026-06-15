(* Inductive data type declaration elaboration. *)

open Elab_common
open Violet_surface
open Violet_common
module Syntax = Violet_kernel.Syntax
module Level = Violet_kernel.Level
module Pretty = Violet_kernel.Pretty
module Evaluation = Wiring.Eval
module Check = Wiring.Check
open Syntax
open Bwd

(* A user-written constructor's type is complete only after the parameters
   of the inductive type are bound implicitly by constructor.
   Let's take an example here:

   \data List (A : U) : U
   | nil : List A

   the type of `List/nil` should be `{A : U} -> List A` *)
let complete_ctor_type
      (params : Surface.pretype Surface.sbinder list)
      (typ : Surface.pretype)
  : Surface.pretype
  =
  List.fold_right
    (fun param acc_ty ->
       { Surface.loc = acc_ty.Surface.loc
       ; node = Surface.Pi ({ param with implicit = true }, acc_ty)
       })
    params
    typ
;;

let bind_constructor
      ~(check_type : local_ctx -> Surface.pretype -> Core.term)
      ~loc
      ~exported
      ~(ind_name : string)
      ~(ind_qname : string)
      ~(module_name : string)
      ~(kernel_module : Violet_kernel.Module.t)
      (ctx : local_ctx)
      (params : Surface.pretype Surface.sbinder list)
      ({ name; bound = typ; _ } : Surface.pretype Surface.sbinder)
  : unit
  =
  let name_loc = Some name.Surface.loc in
  let name = Syntax.Name.to_string name.Surface.value in
  let ctor_typ = complete_ctor_type params typ in
  let ctor_typ_tm = check_type ctx ctor_typ in
  let ctor_typ = Evaluation.eval ctx.env ctor_typ_tm in
  let pp_ty = Notation.pp_term (view_of_ctx ctx) (Evaluation.quote ctx.lvl ctor_typ) in
  let ctor_flat = Syntax.Name.qualify ind_name name in
  (* A constructor inherits its inductive's axiom deps (via the explicit
     [ind_name] ref) plus any axioms mentioned directly in its own type. *)
  Axiom_deps.register_def
    [ ind_name; name ]
    ~refs:(Axiom_deps.refs_in_term ctor_typ_tm @ [ [ ind_name ] ]);
  let ctor_axiom_deps = Axiom_deps.display_deps_of [ ind_name; name ] in
  Observer.emit
    (Def
       { path = [ ind_name; name ]
       ; module_path = Syntax.Name.to_segments module_name
       ; loc
       ; name_loc
       ; ty = ctor_typ
       ; pp_ty
       ; axiom_deps = ctor_axiom_deps
       });
  (* Context: multi-segment for type-directed surface resolution *)
  publish_to_context ~exported [ ind_name; name ] (ctor_typ, `Constructor);
  (* Env: flat key matching the kernel's E.lookup string.
     The Label value carries the BARE name so the eliminator reducer's
     find_ctor_index (which compares against info.ctor_name = bare name) works. *)
  publish_to_env ~exported [ ctor_flat ] (Core.Label (name, Bwd.Emp), `Constructor);
  (* Also register under the bare name so that the unifier's rename/eval
     round-trip (Label x -> Var x -> eval -> lookup x) still finds Label x. *)
  publish_to_env ~exported [ name ] (Core.Label (name, Bwd.Emp), `Constructor);
  let qctor_name = Syntax.Name.of_segments [ module_name; ind_name; name ] in
  Kernel_accept.accept_ctor
    kernel_module
    ~loc
    ~name:qctor_name
    ~data:ind_qname
    ~ty:ctor_typ_tm
;;

let handle_top_data (m : machine) loc data =
  match (data : Surface.top) with
  | Surface.Data { name; params; deps; ind_ty; ctors } ->
    let typ : Surface.pretype =
      List.fold_right
        (fun binding return_ty ->
           { Surface.loc = return_ty.Surface.loc; node = Surface.Pi (binding, return_ty) })
        (params @ deps)
        ind_ty
    in
    push m (KTopData_HaveType { loc; name; params; deps; ind_ty; ctors });
    push m (GInferType typ)
  | _ -> Reporter.fatalf Elab_error "GTopData: payload is not Data"
;;

let handle_top_data_have_type
      ~(check_type : local_ctx -> Surface.pretype -> Core.term)
      (m : machine)
      ~loc
      ~(name : string Surface.spanned)
      ~params
      ~deps
      ~ind_ty
      ~ctors
  =
  let name_loc = Some name.Surface.loc in
  let name = name.Surface.value in
  match take_result m with
  | PType (typ_tm, inferred_sort) ->
    let typ_val = Evaluation.eval m.ctx.env typ_tm in
    let rec final_sort_of_val (ctx_lvl : int) (v : Core.value) : Level.level =
      match Evaluation.force_head v with
      | Core.VPi (_, b) -> final_sort_of_val (ctx_lvl + 1) (b (Core.rigid_local ctx_lvl))
      | Core.Universe l -> l
      | other ->
        Reporter.fatalf
          ~loc
          Elab_error
          "data type `%s`'s spine should end in a Universe, got `%s`"
          name
          (Notation.pp_term (view_of_ctx m.ctx) (Evaluation.quote m.ctx.lvl other))
    in
    let user_sort = final_sort_of_val m.ctx.lvl typ_val in
    let inferred_sort =
      let local_vars = Context.declared_level_vars () in
      let rec subst_foreign l =
        match l with
        | Level.LVar v -> if List.mem v local_vars then l else user_sort
        | Level.LSuc l' -> Level.LSuc (subst_foreign l')
        | Level.LMax (a, b) -> Level.LMax (subst_foreign a, subst_foreign b)
        | Level.LMeta _ ->
          (match Level.force_level l with
           | Level.LMeta _ -> l
           | l' -> subst_foreign l')
        | Level.LZero -> l
      in
      subst_foreign inferred_sort
    in
    if not (Level.le inferred_sort (Level.lsuc user_sort))
    then
      Reporter.fatalf
        ~loc
        Type_error
        "inductive type `%s`'s declared return sort `%s` is not large enough; \
         constructed Pi-tower lives at sort `%s`"
        name
        (Pretty.pp_level user_sort)
        (Pretty.pp_level inferred_sort);
    let lookup_polarity (n : string) : Context.polarity list option =
      match Context.S.resolve [ n ] with
      | Some (_, `Inductive info) -> Some (info : Context.ind_info).param_polarity
      | _ -> None
    in
    Positivity.check_strict_positivity
      ~loc:(Some loc)
      ~ind_name:name
      ~params
      ~deps
      ~lookup_polarity
      ctors;
    let param_polarity =
      Positivity.infer_param_polarity ~ind_name:name ~params ~lookup_polarity ctors
    in
    let infos = List.map (Eliminator_synth.analyze_ctor ~ind_name:name ~params) ctors in
    let ind_info : Context.ind_info =
      { params; deps; ind_ty; ctors; infos; param_polarity }
    in
    let pp_ty =
      Notation.pp_term (view_of_ctx m.ctx) (Evaluation.quote m.ctx.lvl typ_val)
    in
    Axiom_deps.register_def [ name ] ~refs:(Axiom_deps.refs_in_term typ_tm);
    let ind_axiom_deps = Axiom_deps.display_deps_of [ name ] in
    Observer.emit
      (Def
         { path = [ name ]
         ; module_path = Syntax.Name.to_segments m.module_name
         ; loc
         ; name_loc
         ; ty = typ_val
         ; pp_ty
         ; axiom_deps = ind_axiom_deps
         });
    let exported = m.is_exported name in
    publish_to_context ~exported [ name ] (typ_val, `Inductive ind_info);
    publish_to_env ~exported [ name ] (Core.IndType (name, Bwd.Emp), `Constructor);
    let ctor_names =
      List.map
        (fun (b : Surface.pretype Surface.sbinder) ->
           Syntax.Name.to_string b.name.Surface.value)
        ctors
    in
    let qname = Syntax.Name.qualify m.module_name name in
    let qctor_names =
      List.map (fun cn -> Syntax.Name.of_segments [ m.module_name; name; cn ]) ctor_names
    in
    Kernel_accept.accept_data
      m.kernel_module
      ~loc
      ~name:qname
      ~ty:typ_tm
      ~ctor_names:qctor_names;
    List.iter
      (fun ctor ->
         bind_constructor
           ~check_type
           ~loc
           ~exported
           ~ind_name:name
           ~ind_qname:qname
           ~module_name:m.module_name
           ~kernel_module:m.kernel_module
           m.ctx
           params
           ctor)
      ctors;
    let elim_typ : Surface.pretype =
      Eliminator_synth.eliminator_type ~loc ~name ~params ~deps ~ind_ty ctors
    in
    let elim_name = "elim" in
    (* Two-segment path used for namespace resolution in the type context *)
    let elim_path = [ name; elim_name ] in
    let elim_flat = Syntax.Name.qualify name elim_name in
    let elim_typ_tm = check_type m.ctx elim_typ in
    let elim_typ_val = Evaluation.eval m.ctx.env elim_typ_tm in
    publish_to_context ~exported elim_path (elim_typ_val, `Eliminator);
    let reducer_label = elim_flat in
    let reducer =
      Eliminator_synth.build_elim_reducer
        ~ind_name:name
        ~elim_name:reducer_label
        ~params
        ~deps
        ctors
    in
    let elim_head : Core.elim_head = { elim_name = reducer_label; reducer } in
    let elim_value = Core.Elim (elim_head, Bwd.Emp) in
    (* Register in env under the flat key so kernel eval can find it *)
    publish_to_env ~exported [ elim_flat ] (elim_value, `Eliminator);
    let qelim_name = Syntax.Name.of_segments [ m.module_name; name; elim_name ] in
    Kernel_accept.accept_elim
      m.kernel_module
      ~loc
      ~name:qelim_name
      ~ty:elim_typ_tm
      ~reducer:elim_head;
    m.result <- Some PUnit
  | other ->
    Reporter.fatalf Elab_error "KTopData_HaveType: bad result %s" (produced_tag other)
;;
