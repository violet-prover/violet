open Syntax

exception TODO

let eval : Core.term -> Core.value = function
  | Universe -> Universe
  | Var x -> Env.lookup x
  | Meta _ -> Universe
  | InsertedMeta _ -> Universe
  | _ -> raise TODO

let unify (a : Core.value) (b : Core.value) : unit =
  match a, b with
  | _, _ -> raise TODO

let rec check (term : Surface.preterm) (typ : Core.value_ty) : Core.term =
  match term, typ with
  | Lambda (x, body), VPi ({name=x'; typ=a; implicit}, b) -> raise TODO
  | tm, expected_typ ->
    let tm, infer_typ = infer tm in
    unify expected_typ infer_typ;
    tm
and infer : Surface.preterm -> Core.term * Core.value_ty = function
  | Universe -> (Universe, Universe)
  | Var x -> (Var x, Context.lookup x)
  | Pi ({name; typ=a; implicit}, b) ->
    let a = check a Universe in
    (* 引入新的一層 context 並引入 name : A，檢查 B : U *)
    Context.S.section [] @@ fun () ->
    Context.S.import_singleton ( [name], (eval a, `Local));
    let b = check b Universe in
    (Core.Pi ({name; typ=a; implicit}, b), Core.Universe)
  | _ -> raise TODO

let check_module (file : Surface.t) : unit =
  List.iter (fun top ->
    match top with
    | Surface.Let (name, bindings, result_ty, body) ->
      let typ : Surface.pretype = List.fold_left (fun return_ty binding ->
        Surface.Pi (binding, return_ty))
        result_ty
        bindings in
      let typ = check typ Universe in
      let typ = eval typ in

      let variables : string list = List.map (fun (b : Surface.pretype binding) -> b.name) bindings in
      let term : Surface.preterm = List.fold_left (fun body var -> Surface.Lambda (var, body)) body variables in
      let term = check term typ in

      Context.S.include_singleton ~context_visible:`Visible
        ~context_export:`Export
        ([ name ], (typ, `Local));

      Env.S.include_singleton ~context_visible:`Visible
        ~context_export:`Export
        ([name], (eval term, `Local));

      ()
    )
  file.tops
