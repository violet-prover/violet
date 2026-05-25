module L = Linol_eio
module LT = Linol_lsp.Lsp.Types

class violet_lsp ~(sw : Eio.Switch.t) =
  object (self)
    inherit L.Jsonrpc2.server as super
    val store : Doc_store.t = Doc_store.create ()
    val project_index : Project_index.t = Project_index.create ()
    val checker_ref : Checker.t option ref = ref None

    method private checker =
      match !checker_ref with
      | Some c -> c
      | None ->
        let c = Checker.create ~store ~project_index in
        checker_ref := Some c;
        c

    method spawn_query_handler f = L.spawn ~sw f
    method! config_definition = Some (`DefinitionOptions (LT.DefinitionOptions.create ()))
    method! config_hover = Some (`HoverOptions (LT.HoverOptions.create ()))

    method! config_modify_capabilities c =
      { c with referencesProvider = Some (`Bool true) }

    method
      private recheck_and_publish
      ~(notify_back : L.Jsonrpc2.notify_back)
      (uri : LT.DocumentUri.t)
      : unit =
      Checker.recheck self#checker ~uri;
      match Doc_store.find store ~uri with
      | None -> ()
      | Some d ->
        let diags = !(d.snapshot).diagnostics in
        notify_back#send_diagnostic diags

    method on_notif_doc_did_open ~notify_back (d : LT.TextDocumentItem.t) ~content : unit
        =
      let _ = Doc_store.update store ~uri:d.uri ~text:content ~version:d.version in
      self#recheck_and_publish ~notify_back d.uri

    method on_notif_doc_did_change
      ~notify_back
      (d : LT.VersionedTextDocumentIdentifier.t)
      _changes
      ~old_content:_
      ~new_content
      : unit =
      let _ = Doc_store.update store ~uri:d.uri ~text:new_content ~version:d.version in
      self#recheck_and_publish ~notify_back d.uri

    method on_notif_doc_did_close ~notify_back:_ (d : LT.TextDocumentIdentifier.t) : unit
        =
      Doc_store.remove store ~uri:d.uri

    method! on_req_hover
      ~notify_back:_
      ~id:_
      ~uri
      ~pos
      ~workDoneToken:_
      (_ : L.doc_state)
      : LT.Hover.t option =
      Hover.handle store ~uri ~position:pos

    method! on_req_definition
      ~notify_back:_
      ~id:_
      ~uri
      ~pos
      ~workDoneToken:_
      ~partialResultToken:_
      (_ : L.doc_state)
      : LT.Locations.t option =
      match Definition.handle store project_index self#checker ~uri ~position:pos with
      | [] -> None
      | locs -> Some (`Location locs)

    method! on_request_unhandled
      : type r. notify_back:_ -> id:_ -> r Linol_lsp.Lsp.Client_request.t -> r =
      fun ~notify_back ~id r ->
        match r with
        | Linol_lsp.Lsp.Client_request.TextDocumentReferences p ->
          let uri = p.textDocument.uri in
          let position = p.position in
          let locs = References.handle store ~uri ~position in
          (match locs with
           | [] -> None
           | ls -> Some ls)
        | _ -> super#on_request_unhandled ~notify_back ~id r
  end

let run ~env () =
  Eio.Switch.run
  @@ fun sw ->
  let s = new violet_lsp ~sw in
  let server = L.Jsonrpc2.create_stdio ~env s in
  let task () =
    let shutdown () = s#get_status = `ReceivedExit in
    L.Jsonrpc2.run ~shutdown server
  in
  match task () with
  | () -> ()
  | exception e ->
    let e = Printexc.to_string e in
    Printf.eprintf "violet lsp error: %s\n%!" e;
    exit 1
;;
