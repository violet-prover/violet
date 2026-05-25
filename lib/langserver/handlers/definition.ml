let handle
      (store : Doc_store.t)
      (_project_index : Project_index.t)
      (checker : Checker.t)
      ~uri
      ~(position : Linol_lsp.Lsp.Types.Position.t)
  : Linol_lsp.Lsp.Types.Location.t list
  =
  match Doc_store.find store ~uri with
  | None -> []
  | Some d ->
    let filename = Linol_lsp.Lsp.Types.DocumentUri.to_path uri in
    let idx = !(d.snapshot).index in
    let line = position.line + 1 in
    let col = position.character in
    let result =
      Violet_interactive.Query.goto_definition ~source:filename ~line ~col idx
    in
    (match result with
     | None -> []
     | Some { loc; _ } ->
       let target_file = Violet_interactive.Index.source_of_range loc in
       let target_uri =
         match target_file with
         | Some f when f <> filename ->
           Checker.ensure_indexed checker ~file:f;
           Linol_lsp.Lsp.Types.DocumentUri.of_path f
         | _ -> uri
       in
       [ Linol_lsp.Lsp.Types.Location.create
           ~uri:target_uri
           ~range:(Diagnostics.lsp_range_of_asai loc)
       ])
;;
