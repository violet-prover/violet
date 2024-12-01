open Syntax
open Bwd
open Evaluation

module Bound = struct
  type t = string bwd
end

module BoundState = Algaeff.State.Make (Bound)

let rec check ~loc (term : Surface.preterm) (typ : Core.value_ty) : Core.term =
  match term, typ with
  | ( Lambda { name = x; bound = body; implicit = lambda_mode }
    , VPi ({ name = _; bound = a; implicit = pi_mode }, b) ) ->
    if lambda_mode != pi_mode
    then Reporter.fatalf ~loc Elab_error "mode mismatching"
    else
      Context.S.section []
      @@ fun () ->
      Context.S.import_singleton ([ x ], (a, `Local));
      let body = check ~loc body (b (Rigid (x, Emp))) in
      Core.Lambda { name = x; bound = body; implicit = lambda_mode }
  | Hole, _ -> Meta.fresh (BoundState.get ())
  | tm, expected_typ ->
    let tm, infer_typ = infer ~loc tm in
    Unification.unify ~loc expected_typ infer_typ;
    tm

(* infer 的用途是，把已經裝飾過的 surface term 變成 core term，並且推導其型別，這個過程可以失敗 *)
and infer ~loc : Surface.preterm -> Core.term * Core.value_ty = function
  | Located { loc; value } -> infer ~loc:(Option.get loc) value
  | Universe -> Universe, Universe
  | Var x -> Var x, Context.lookup x
  | Pi ({ name; bound = a; implicit }, b) ->
    let a = check ~loc a Universe in
    (* 引入一層 x = x 的 environment *)
    Env.S.section []
    @@ fun () ->
    Env.S.include_singleton ([ name ], (Rigid (name, Bwd.Emp), `Local));
    (* 引入新的一層 context 並引入 name : A，檢查 B : U *)
    Context.S.section []
    @@ fun () ->
    Context.S.include_singleton ([ name ], (eval a, `Local));
    let b = check ~loc b Universe in
    Core.Pi ({ name; bound = a; implicit }, b), Core.Universe
  | App (is_implicit, f, arg) ->
    let f', f_typ = infer ~loc f in
    (match f_typ with
     | VPi ({ implicit; name = _; bound = a }, b) ->
       if is_implicit == implicit
       then (
         let arg' = check ~loc arg a in
         App (f', arg'), b @@ eval arg')
       else if implicit
       then infer ~loc @@ App (false, App (implicit, f, Hole), arg)
       else
         Reporter.fatalf
           ~loc
           Elab_error
           "Bad apply %s %s"
           ([%show: Surface.preterm] f)
           ([%show: Surface.preterm] arg)
     | ty ->
       Reporter.fatalf
         ~loc
         Type_error
         "cannot apply a value to something with type `%s`"
         ([%show: Core.value_ty] ty))
  | Hole ->
    let ty = eval @@ Meta.fresh (BoundState.get ()) in
    let t = Meta.fresh (BoundState.get ()) in
    t, ty
  | Lambda _ -> Reporter.fatalf ~loc Elab_error "cannot infer lambda term"
;;

let check_top ~loc top =
  match top with
  | Surface.Data { name; _ } ->
    Reporter.tracef ~loc "checking an inductive data type %s" name
    @@ fun () -> Reporter.fatalf ~loc TODO "todo"
  | Surface.Let (name, bindings, result_ty, body) ->
    BoundState.set @@ Bwd.of_list (List.map (fun b -> b.name) bindings);
    let typ : Surface.pretype =
      List.fold_right
        (fun binding return_ty -> Surface.Pi (binding, return_ty))
        bindings
        result_ty
    in
    Reporter.tracef
      ~loc
      "while checking a top let %s : %s"
      name
      ([%show: Surface.pretype] typ)
    @@ fun () ->
    let typ = Context.S.section [] @@ fun () -> check ~loc typ Universe in
    let typ = Env.S.section [] @@ fun () -> eval typ in
    let term : Surface.preterm =
      List.fold_right
        (fun { name; implicit; bound = _ } body ->
          Surface.Lambda { name; bound = body; implicit })
        bindings
        body
    in
    let term = Context.S.section [] @@ fun () -> check ~loc term typ in
    Context.S.include_singleton
      ~context_visible:`Visible
      ~context_export:`Export
      ([ name ], (typ, `Local));
    Env.S.include_singleton
      ~context_visible:`Visible
      ~context_export:`Export
      ([ name ], Env.S.section [] @@ fun () -> eval term, `Local);
    ()
;;

let check_module (file : Surface.t) : unit =
  BoundState.run ~init:Emp
  @@ fun () ->
  List.iter
    (fun (top : Surface.top Asai.Range.located) ->
      let loc = Option.get top.loc in
      check_top ~loc top.value)
    file.tops
;;
