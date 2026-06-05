let handle (store : Doc_store.t) ~uri ~(position : Linol_lsp.Lsp.Types.Position.t)
  : Linol_lsp.Lsp.Types.Location.t list
  =
  match Doc_store.find store ~uri with
  | None -> []
  | Some d ->
    let filename = Linol_lsp.Lsp.Types.DocumentUri.to_path uri in
    let idx = !(d.snapshot).index in
    let line = position.line + 1 in
    let col =
      Encoding.utf16_to_byte
        ~line_text:(Encoding.line_text ~doc:d.text ~line)
        position.character
    in
    let refs = Violet_interactive.Query.find_references ~source:filename ~line ~col idx in
    List.filter_map
      (fun (r : Violet_interactive.Query.reference) ->
         (* A reference can live in any file of the dep graph, not just the open
            doc. Resolve each location's own source file, build its URI from that
            path, and encoding-convert its range with that file's text. *)
         match Violet_interactive.Index.source_of_range r.loc with
         | None ->
           (* Synthetic (`String) source — not a real file; drop it. *)
           None
         | Some file ->
           let target_uri = Linol_lsp.Lsp.Types.DocumentUri.of_path file in
           (* If the target file's text is unavailable, fall back to the
              unconverted byte columns (degraded, not dropped). *)
           let range =
             match Doc_store.text_of_file store ~file with
             | Some text -> Diagnostics.lsp_range_of_asai ~text r.loc
             | None -> Diagnostics.lsp_range_of_asai r.loc
           in
           Some (Linol_lsp.Lsp.Types.Location.create ~uri:target_uri ~range))
      refs
;;
