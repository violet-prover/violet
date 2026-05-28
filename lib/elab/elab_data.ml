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
let complete_ctor_type (params : Surface.pretype binder list) (typ : Surface.pretype)
  : Surface.pretype
  =
  List.fold_right
    (fun param acc_ty -> Surface.Pi ({ param with implicit = true }, acc_ty))
    params
    typ
;;

let bind_constructor
      ~(check_type : loc:Asai.Range.t -> local_ctx -> Surface.pretype -> Core.term)
      ~loc
      ~(name_loc : Asai.Range.t option)
      ~exported
      ~(ind_name : string)
      ~(ind_qname : string)
      ~(module_name : string)
      ~(kernel_module : Violet_kernel.Module.t)
      (ctx : local_ctx)
      (params : Surface.pretype binder list)
      ({ name; bound = typ; _ } : Surface.pretype binder)
  : unit
  =
  let name = Syntax.Name.to_string name in
  let ctor_typ = complete_ctor_type params typ in
  let ctor_typ_tm = check_type ~loc ctx ctor_typ in
  let ctor_typ = Evaluation.eval ctx.env ctor_typ_tm in
  let pp_ty = Pretty.pp_term (view_of_ctx ctx) (Evaluation.quote ctx.lvl ctor_typ) in
  Observer.emit (Def { path = [ ind_name; name ]; loc; name_loc; ty = ctor_typ; pp_ty });
  let ctor_flat = ind_name ^ "/" ^ name in
  (* Context: multi-segment for type-directed surface resolution *)
  publish_to_context ~exported [ ind_name; name ] (ctor_typ, `Constructor);
  (* Env: flat key matching the kernel's E.lookup string.
     The Label value carries the BARE name so the eliminator reducer's
     find_ctor_index (which compares against info.ctor_name = bare name) works. *)
  publish_to_env ~exported [ ctor_flat ] (Core.Label (name, Bwd.Emp), `Constructor);
  (* Also register under the bare name so that the unifier's rename/eval
     round-trip (Label x -> Var x -> eval -> lookup x) still finds Label x. *)
  publish_to_env ~exported [ name ] (Core.Label (name, Bwd.Emp), `Constructor);
  let qctor_name = module_name ^ "." ^ ind_name ^ "." ^ name in
  Kernel_accept.accept_ctor
    kernel_module
    ~loc
    ~name:qctor_name
    ~data:ind_qname
    ~ty:ctor_typ_tm
;;

let handle_top_data (m : machine) loc data =
  match (data : Surface.top) with
  | Surface.Data
      { name; name_loc; params; deps; ind_ty; ind_ty_loc; ctors; ctor_name_locs } ->
    let ind_ty_for_elab =
      match ind_ty_loc with
      | Some l -> Surface.Located { loc = Some l; value = ind_ty }
      | None -> ind_ty
    in
    let typ : Surface.pretype =
      List.fold_right
        (fun binding return_ty -> Surface.Pi (binding, return_ty))
        (params @ deps)
        ind_ty_for_elab
    in
    push
      m
      (KTopData_HaveType
         { loc; name; name_loc; params; deps; ind_ty; ctors; ctor_name_locs });
    push m (GInferType (loc, typ))
  | _ -> Reporter.fatalf Elab_error "GTopData: payload is not Data"
;;

let handle_top_data_have_type
      ~(check_type : loc:Asai.Range.t -> local_ctx -> Surface.pretype -> Core.term)
      ~(check_term_against :
         loc:Asai.Range.t -> local_ctx -> Surface.preterm -> Core.value -> Core.term)
      (m : machine)
      ~loc
      ~name
      ~name_loc
      ~params
      ~deps
      ~ind_ty
      ~ctors
      ~ctor_name_locs
  =
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
          (Pretty.pp_term (view_of_ctx m.ctx) (Evaluation.quote m.ctx.lvl other))
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
    let pp_ty = Pretty.pp_term (view_of_ctx m.ctx) (Evaluation.quote m.ctx.lvl typ_val) in
    Observer.emit (Def { path = [ name ]; loc; name_loc; ty = typ_val; pp_ty });
    let exported = m.is_exported name in
    publish_to_context ~exported [ name ] (typ_val, `Inductive ind_info);
    publish_to_env ~exported [ name ] (Core.IndType (name, Bwd.Emp), `Constructor);
    let ctor_names =
      List.map (fun (b : Surface.pretype binder) -> Syntax.Name.to_string b.name) ctors
    in
    let qname = m.module_name ^ "." ^ name in
    let qctor_names =
      List.map (fun cn -> m.module_name ^ "." ^ name ^ "." ^ cn) ctor_names
    in
    Kernel_accept.accept_data
      m.kernel_module
      ~loc
      ~name:qname
      ~ty:typ_tm
      ~ctor_names:qctor_names;
    List.iter2
      (fun ctor_name_loc ctor ->
         bind_constructor
           ~check_type
           ~loc
           ~name_loc:ctor_name_loc
           ~exported
           ~ind_name:name
           ~ind_qname:qname
           ~module_name:m.module_name
           ~kernel_module:m.kernel_module
           m.ctx
           params
           ctor)
      ctor_name_locs
      ctors;
    let elim_typ : Surface.pretype =
      Eliminator_synth.eliminator_type ~name ~params ~deps ~ind_ty ctors
    in
    let elim_name = "elim" in
    (* Two-segment path used for namespace resolution in the type context *)
    let elim_path = [ name; elim_name ] in
    let elim_flat = name ^ "/" ^ elim_name in
    let elim_typ_tm = check_type ~loc m.ctx elim_typ in
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
    let qelim_name = m.module_name ^ "." ^ name ^ "." ^ elim_name in
    Kernel_accept.accept_elim
      m.kernel_module
      ~loc
      ~name:qelim_name
      ~ty:elim_typ_tm
      ~reducer:elim_head;
    if
      false
      && params = []
      && deps = []
      && Context.has "Id"
      && Context.has "subst"
      && Context.has "Empty"
      && Context.has "Sigma"
    then (
      let publish_def nc_name nc_typ_tm nc_typ_val nc_body_tm nc_body_val =
        publish_to_context ~exported [ nc_name ] (nc_typ_val, `Defn);
        publish_to_context ~exported [ name; nc_name ] (nc_typ_val, `Defn);
        let nc_flat = name ^ "/" ^ nc_name in
        publish_to_env ~exported [ nc_flat ] (nc_body_val, `Defn);
        Env.register_definition nc_flat nc_body_val;
        let qnc_name = m.module_name ^ "." ^ name ^ "." ^ nc_name in
        Kernel_accept.accept_let
          m.kernel_module
          ~loc
          ~name:qnc_name
          ~ty:nc_typ_tm
          ~body:nc_body_tm
      in
      let nct_typ, nct_body = Eliminator_synth.no_confusion_type_def ~name ~ctors in
      let nct_typ_tm = check_type ~loc m.ctx nct_typ in
      let nct_typ_val = Evaluation.eval m.ctx.env nct_typ_tm in
      let nct_body_tm = check_term_against ~loc m.ctx nct_body nct_typ_val in
      let nct_body_val = Evaluation.eval m.ctx.env nct_body_tm in
      publish_def "no-confusion-type" nct_typ_tm nct_typ_val nct_body_tm nct_body_val;
      let nc_typ, nc_body = Eliminator_synth.no_confusion_def ~name ~ctors in
      let nc_typ_tm = check_type ~loc m.ctx nc_typ in
      let nc_typ_val = Evaluation.eval m.ctx.env nc_typ_tm in
      let nc_body_tm = check_term_against ~loc m.ctx nc_body nc_typ_val in
      let nc_body_val = Evaluation.eval m.ctx.env nc_body_tm in
      publish_def "no-confusion" nc_typ_tm nc_typ_val nc_body_tm nc_body_val);
    m.result <- Some PUnit
  | other ->
    Reporter.fatalf
      Elab_error
      "KTopData_HaveType: bad result %s"
      ([%show: produced] other)
;;
