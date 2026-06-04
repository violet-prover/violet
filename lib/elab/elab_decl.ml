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

let handle_universe_decl (m : machine) (names : string Surface.spanned list) =
  List.iter
    (fun (n : string Surface.spanned) ->
       let name = n.Surface.value in
       let loc = n.Surface.loc in
       Context.declare_level_var name;
       let ty = Core.Universe (Level.LSuc (Level.LVar name)) in
       let pp_ty = Pretty.pp_level (Level.LSuc (Level.LVar name)) in
       Observer.emit (Def { path = [ name ]; loc; name_loc = Some loc; ty; pp_ty }))
    names;
  m.result <- Some PUnit
;;

let handle_top_let (m : machine) ~loc ~name ~bindings ~result_ty ~body =
  let typ : Surface.pretype =
    List.fold_right
      (fun (binding : Surface.pretype Surface.sbinder) return_ty ->
         { Surface.loc = return_ty.Surface.loc; node = Surface.Pi (binding, return_ty) })
      bindings
      result_ty
  in
  push m (KTopLet_HaveType { loc; name; body; bindings });
  push m (GInferType typ)
;;

let handle_top_let_have_type (m : machine) ~loc ~name ~body ~bindings =
  match take_result m with
  | PType (typ_tm, _) ->
    let typ_val = Evaluation.eval m.ctx.env typ_tm in
    let term : Surface.preterm =
      List.fold_right
        (fun ({ name; implicit; bound = _ } : Surface.pretype Surface.sbinder) body ->
           { Surface.loc = Surface.join_loc name.Surface.loc body.Surface.loc
           ; node = Surface.Lambda { name; bound = body; implicit }
           })
        bindings
        body
    in
    push m (KTopLet_HaveBody { loc; name; typ_tm; typ_val });
    push m (GCheck (term, typ_val))
  | other ->
    Reporter.fatalf Elab_error "KTopLet_HaveType: bad result %s" (produced_tag other)
;;

let handle_top_let_have_body
      (m : machine)
      ~loc
      ~(name : string Surface.spanned)
      ~typ_tm
      ~typ_val
  =
  match take_result m with
  | PTerm term ->
    let pp_ty = Pretty.pp_term (view_of_ctx m.ctx) (Evaluation.quote m.ctx.lvl typ_val) in
    Observer.emit
      (Def
         { path = [ name.Surface.value ]
         ; loc
         ; name_loc = Some name.Surface.loc
         ; ty = typ_val
         ; pp_ty
         });
    let exported = m.is_exported name.Surface.value in
    publish_to_context ~exported [ name.Surface.value ] (typ_val, `Defn);
    let body_val = Evaluation.eval m.ctx.env term in
    publish_to_env ~exported [ name.Surface.value ] (body_val, `Defn);
    Env.register_definition name.Surface.value body_val;
    let qname = m.module_name ^ "." ^ name.Surface.value in
    Kernel_accept.accept_let m.kernel_module ~loc ~name:qname ~ty:typ_tm ~body:term;
    m.result <- Some PUnit
  | other ->
    Reporter.fatalf Elab_error "KTopLet_HaveBody: bad result %s" (produced_tag other)
;;
