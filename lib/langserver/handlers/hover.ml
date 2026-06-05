let render_type ~name ~ty =
  match ty with
  | Some t -> Printf.sprintf "```violet\n%s : %s\n```" name t
  | None -> Printf.sprintf "```violet\n%s\n```" name
;;

let render_goal ~name ~ctx ~target =
  let buf = Buffer.create 128 in
  Buffer.add_string buf (Printf.sprintf "```violet\n?%s\n--- context ---\n" name);
  List.iter (fun (n, ty) -> Buffer.add_string buf (Printf.sprintf "%s : %s\n" n ty)) ctx;
  Buffer.add_string buf (Printf.sprintf "--- target ---\n%s\n```" target);
  Buffer.contents buf
;;

let mk_hover value =
  Linol_lsp.Lsp.Types.Hover.create
    ~contents:
      (`MarkupContent (Linol_lsp.Lsp.Types.MarkupContent.create ~kind:Markdown ~value))
    ()
;;

let handle (store : Doc_store.t) ~uri ~(position : Linol_lsp.Lsp.Types.Position.t)
  : Linol_lsp.Lsp.Types.Hover.t option
  =
  match Doc_store.find store ~uri with
  | None -> None
  | Some d ->
    let filename = Linol_lsp.Lsp.Types.DocumentUri.to_path uri in
    let idx = !(d.snapshot).index in
    let line = position.line + 1 in
    let col =
      Encoding.utf16_to_byte
        ~line_text:(Encoding.line_text ~doc:d.text ~line)
        position.character
    in
    (match Violet_interactive.Index.find_at ~source:filename ~line ~col idx with
     | Some { kind = Def; path; pp_ty; _ } | Some { kind = Use; path; pp_ty; _ } ->
       let name = String.concat "/" path in
       Some (mk_hover (render_type ~name ~ty:pp_ty))
     | Some { kind = Goal; path; ctx; pp_target = Some target; _ } ->
       let name = String.concat "/" path in
       Some (mk_hover (render_goal ~name ~ctx ~target))
     | Some { kind = Goal; path; pp_target = None; _ } ->
       let name = String.concat "/" path in
       Some (mk_hover (render_type ~name ~ty:None))
     | Some { kind = Binder; path; pp_ty; _ } ->
       let name = String.concat "/" path in
       Some (mk_hover (render_type ~name ~ty:pp_ty))
     | None -> None)
;;
