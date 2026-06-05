(* Get the full text of [file]: prefer the in-memory Doc_store copy if the file
   is currently open, otherwise read it from disk. Returns [None] if neither is
   available (e.g. the file was deleted). *)
let text_of_file (store : Doc_store.t) ~file : string option =
  let uri = Linol_lsp.Lsp.Types.DocumentUri.of_path file in
  match Doc_store.find store ~uri with
  | Some d -> Some d.text
  | None ->
    (try
       let ic = open_in_bin file in
       Fun.protect
         ~finally:(fun () -> close_in_noerr ic)
         (fun () -> Some (In_channel.input_all ic))
     with
     | Sys_error _ -> None)
;;

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
    let col =
      Encoding.utf16_to_byte
        ~line_text:(Encoding.line_text ~doc:d.text ~line)
        position.character
    in
    let result =
      Violet_interactive.Query.goto_definition ~source:filename ~line ~col idx
    in
    (match result with
     | None -> []
     | Some { loc; _ } ->
       let target_file = Violet_interactive.Index.source_of_range loc in
       let target_uri, target_text =
         match target_file with
         | Some f when f <> filename ->
           Checker.ensure_indexed checker ~file:f;
           Linol_lsp.Lsp.Types.DocumentUri.of_path f, text_of_file store ~file:f
         | _ -> uri, Some d.text
       in
       (* Convert the target byte range back to UTF-16. If the target file's
          text is unavailable, fall back to the unconverted byte columns. *)
       let range =
         match target_text with
         | Some text -> Diagnostics.lsp_range_of_asai ~text loc
         | None -> Diagnostics.lsp_range_of_asai loc
       in
       [ Linol_lsp.Lsp.Types.Location.create ~uri:target_uri ~range ])
;;
