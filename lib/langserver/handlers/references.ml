let handle (store : Doc_store.t) ~uri ~(position : Linol_lsp.Lsp.Types.Position.t)
  : Linol_lsp.Lsp.Types.Location.t list
  =
  match Doc_store.find store ~uri with
  | None -> []
  | Some d ->
    let filename = Linol_lsp.Lsp.Types.DocumentUri.to_path uri in
    let idx = !(d.snapshot).index in
    let line = position.line + 1 in
    let col = position.character in
    let refs = Violet_interactive.Query.find_references ~source:filename ~line ~col idx in
    List.map
      (fun (r : Violet_interactive.Query.reference) ->
         Linol_lsp.Lsp.Types.Location.create
           ~uri
           ~range:(Diagnostics.lsp_range_of_asai r.loc))
      refs
;;
