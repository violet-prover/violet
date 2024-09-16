open Syntax

exception TODO

let rec check (term : Surface.preterm) (typ : Core.value_ty) : Core.term =
  match term, typ with
  | Universe, Universe -> Universe
  | Var x, typ -> raise TODO
  | Lambda (x, body), typ -> raise TODO
  | Pi (bind, b) -> raise TODO

let eval : Core.term -> Core.value = function
  | Universe -> Universe
  | Var x ->
    begin
      match Env.S.resolve [x] with
      | Some (v, _) -> v
      | None -> Reporter.fatalf NoVar_error "cannot find `%s` in environment"
        (String.concat " " [x])
    end
  | Meta _ -> Universe
  | InsertedMeta _ -> Universe

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

      let variables : string list = List.map (fun (b : Surface.binding) -> b.name) bindings in
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
