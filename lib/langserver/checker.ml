type t =
  { store : Doc_store.t
  ; project_index : Project_index.t
  }

let create ~store ~project_index : t = { store; project_index }

let recheck (t : t) ~uri : unit =
  match Doc_store.find t.store ~uri with
  | None -> ()
  | Some d ->
    let filename = Linol_lsp.Lsp.Types.DocumentUri.to_path uri in
    let module_path = !(d.snapshot).module_path in
    let diags : Linol_lsp.Lsp.Types.Diagnostic.t list ref = ref [] in
    let collector = Violet_interactive.Collector.create () in
    let aborted = ref false in
    let emit (diag : Violet_common.Reporter.Message.t Asai.Diagnostic.t) =
      diags := Diagnostics.lsp_of_asai diag :: !diags
    in
    let fatal (diag : Violet_common.Reporter.Message.t Asai.Diagnostic.t) =
      diags := Diagnostics.lsp_of_asai diag :: !diags;
      aborted := true;
      raise Exit
    in
    let text_override path = if path = filename then Some d.text else None in
    let on_event = Violet_interactive.Collector.on_event collector in
    (try
       Violet_common.Reporter.run ~emit ~fatal (fun () ->
         let open Violet_elab in
         Context.S.run
           ~shadow:Context.Handler.shadow
           ~not_found:Context.Handler.not_found
           ~hook:Context.Handler.hook
         @@ fun () ->
         Env.S.run
           ~shadow:Env.Handler.shadow
           ~not_found:Env.Handler.not_found
           ~hook:Env.Handler.hook
         @@ fun () ->
         let m = Violet_surface.Parser.parse_buffer ~filename d.text in
         let deps = Hashtbl.create 16 in
         let mods = Hashtbl.create 16 in
         let mode = Violet_project.Loader.mode_for_entry filename in
         Violet_project.Loader.prepare_dependencies
           ~text_override
           mode
           []
           mods
           deps
           (Violet_project.Loader.module_name filename)
           m;
         match Tsort.sort @@ List.of_seq @@ Hashtbl.to_seq deps with
         | Sorted r ->
           List.iter
             (fun mn ->
                let mp = String.split_on_char '/' mn in
                Elab.check_module ~on_event ~module_path:mp (Hashtbl.find mods mn))
             r
         | ErrorCycle _ -> ())
     with
     | Exit -> ());
    let new_index = Violet_interactive.Collector.to_index collector in
    let prev_last_good = !(d.snapshot).last_good_index in
    let last_good = if !aborted then prev_last_good else new_index in
    d.snapshot
    := { module_path
       ; diagnostics = List.rev !diags
       ; index = new_index
       ; last_good_index = last_good
       };
    Project_index.update t.project_index ~file:filename ~index:new_index
;;

let ensure_indexed (t : t) ~file : unit =
  match Project_index.find_by_file t.project_index ~file with
  | Some _ -> ()
  | None ->
    let collector = Violet_interactive.Collector.create () in
    let on_event = Violet_interactive.Collector.on_event collector in
    (try
       Violet_common.Reporter.run
         ~emit:(fun _ -> ())
         ~fatal:(fun _ -> raise Exit)
         (fun () ->
            let open Violet_elab in
            Context.S.run
              ~shadow:Context.Handler.shadow
              ~not_found:Context.Handler.not_found
              ~hook:Context.Handler.hook
            @@ fun () ->
            Env.S.run
              ~shadow:Env.Handler.shadow
              ~not_found:Env.Handler.not_found
              ~hook:Env.Handler.hook
            @@ fun () ->
            let m = Violet_surface.Parser.parse_file file in
            let module_path = [ Violet_project.Loader.module_name file ] in
            Elab.check_module ~on_event ~module_path m)
     with
     | Exit -> ());
    let idx = Violet_interactive.Collector.to_index collector in
    Project_index.update t.project_index ~file ~index:idx
;;

let%expect_test "recheck of clean buffer populates index" =
  let store = Doc_store.create () in
  let project_index = Project_index.create () in
  let uri = Linol_lsp.Lsp.Types.DocumentUri.of_path "/tmp/Demo.vt" in
  let text =
    {|\universe U
\let f (A : U) : U => A
\let g (A : U) : U => f A
|}
  in
  let _ = Doc_store.update store ~uri ~text ~version:1 in
  let c = create ~store ~project_index in
  recheck c ~uri;
  let d = Option.get (Doc_store.find store ~uri) in
  let snap = !(d.snapshot) in
  let has_entries = List.length (Violet_interactive.Index.all_entries snap.index) > 0 in
  Printf.printf "diags=%d has_entries=%b" (List.length snap.diagnostics) has_entries;
  [%expect
    {|
    +checking [module] Demo (/tmp/Demo.vt)
    diags=0 has_entries=true
  |}]
;;

let%expect_test "recheck of broken buffer preserves last_good_index" =
  let store = Doc_store.create () in
  let project_index = Project_index.create () in
  let uri = Linol_lsp.Lsp.Types.DocumentUri.of_path "/tmp/Broken.vt" in
  let good =
    {|\universe U
\let f (A : U) : U => A
|}
  in
  let _ = Doc_store.update store ~uri ~text:good ~version:1 in
  let c = create ~store ~project_index in
  recheck c ~uri;
  let good_count =
    List.length
      (Violet_interactive.Index.all_entries
         !((Option.get (Doc_store.find store ~uri)).snapshot).index)
  in
  let broken =
    {|\universe U
\let f : U => not_a_real_ident
|}
  in
  let _ = Doc_store.update store ~uri ~text:broken ~version:2 in
  recheck c ~uri;
  let snap = !((Option.get (Doc_store.find store ~uri)).snapshot) in
  let last_good_count =
    List.length (Violet_interactive.Index.all_entries snap.last_good_index)
  in
  Printf.printf
    "diags>0=%b preserved=%b"
    (List.length snap.diagnostics > 0)
    (last_good_count = good_count);
  [%expect
    {|
    +checking [module] Broken (/tmp/Broken.vt)
    +checking [module] Broken (/tmp/Broken.vt)
    diags>0=true preserved=true
  |}]
;;
