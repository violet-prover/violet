(* Declaration elaboration: universe declarations and let bindings. *)

open Elab_common
open Violet_surface
open Violet_common
module Syntax = Violet_kernel.Syntax
module Level = Violet_kernel.Level
module Pretty = Violet_kernel.Pretty
module Evaluation = Wiring.Eval
module Check = Wiring.Check
open Syntax

let handle_universe_decl (m : machine) names =
  List.iter
    (fun (name, loc) ->
       Context.declare_level_var name;
       match loc with
       | Some loc ->
         let ty = Core.Universe (Level.LSuc (Level.LVar name)) in
         let pp_ty = Pretty.pp_level (Level.LSuc (Level.LVar name)) in
         Observer.emit (Def { path = [ name ]; loc; name_loc = Some loc; ty; pp_ty })
       | None -> ())
    names;
  m.result <- Some PUnit
;;

let handle_top_let (m : machine) ~loc ~name ~name_loc ~bindings ~result_ty ~body =
  let typ : Surface.pretype =
    List.fold_right
      (fun binding return_ty -> Surface.Pi (binding, return_ty))
      bindings
      result_ty
  in
  push m (KTopLet_HaveType { loc; name; name_loc; body; bindings });
  push m (GInferType (loc, typ))
;;

let handle_top_let_have_type (m : machine) ~loc ~name ~name_loc ~body ~bindings =
  match take_result m with
  | PType (typ_tm, _) ->
    let typ_val = Evaluation.eval m.ctx.env typ_tm in
    let term : Surface.preterm =
      List.fold_right
        (fun { name; implicit; bound = _ } body ->
           Surface.Lambda { name; bound = body; implicit })
        bindings
        body
    in
    push m (KTopLet_HaveBody { loc; name; name_loc; typ_tm; typ_val });
    push m (GCheck (loc, term, typ_val))
  | other ->
    Reporter.fatalf Elab_error "KTopLet_HaveType: bad result %s" (produced_tag other)
;;

let handle_top_let_have_body (m : machine) ~loc ~name ~name_loc ~typ_tm ~typ_val =
  match take_result m with
  | PTerm term ->
    let pp_ty = Pretty.pp_term (view_of_ctx m.ctx) (Evaluation.quote m.ctx.lvl typ_val) in
    Observer.emit (Def { path = [ name ]; loc; name_loc; ty = typ_val; pp_ty });
    let exported = m.is_exported name in
    publish_to_context ~exported [ name ] (typ_val, `Defn);
    let body_val = Evaluation.eval m.ctx.env term in
    publish_to_env ~exported [ name ] (body_val, `Defn);
    Env.register_definition name body_val;
    let qname = m.module_name ^ "." ^ name in
    Kernel_accept.accept_let m.kernel_module ~loc ~name:qname ~ty:typ_tm ~body:term;
    m.result <- Some PUnit
  | other ->
    Reporter.fatalf Elab_error "KTopLet_HaveBody: bad result %s" (produced_tag other)
;;
