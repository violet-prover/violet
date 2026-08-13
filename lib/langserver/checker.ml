type t =
  { store : Doc_store.t
  ; project_index : Project_index.t
  }

let create ~store ~project_index : t = { store; project_index }

(* A literate [.vt.scrbl] card is a scribble document: elaborate the
   synthesized module (its [@vt|{}|] blocks concatenated) under the card's
   [.vt] name, then remap diagnostics back onto the scrbl text. For a plain
   [.vt] buffer [module_file] is [filename] and the literate steps are
   no-ops. *)
let is_scrbl filename = Filename.check_suffix filename ".vt.scrbl"

let recheck (t : t) ~uri : unit =
  match Doc_store.find t.store ~uri with
  | None -> ()
  | Some d ->
    let filename = Linol_lsp.Lsp.Types.DocumentUri.to_path uri in
    let module_path = !(d.snapshot).module_path in
    let module_file =
      if is_scrbl filename then Filename.chop_extension filename else filename
    in
    let buffer = ref d.text in
    let blocks = ref [] in
    let diag_collector = Violet_common.Diagnostic_collector.create () in
    let collector = Violet_interactive.Collector.create () in
    let aborted = ref false in
    let emit (diag : Violet_common.Reporter.Message.t Asai.Diagnostic.t) =
      Violet_common.Diagnostic_collector.emit diag_collector diag
    in
    let fatal (diag : Violet_common.Reporter.Message.t Asai.Diagnostic.t) =
      emit diag;
      aborted := true;
      raise Exit
    in
    (* Override the entry module's on-disk text with the in-editor buffer (the
       synthesized code for a card, the raw text for a plain [.vt]). *)
    let text_override path =
      if String.equal path module_file then Some !buffer else None
    in
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
         let mode = Violet_project.Loader.mode_for_entry module_file in
         let m =
           if is_scrbl filename
           then begin
             let rules = Violet_literate.Weave.literate_rules_for mode filename in
             let delim, _output = Violet_literate.Delim.resolve ~path:filename rules in
             let _, buf, blks =
               Violet_literate.Source.to_buffer ~delim ~source:filename d.text
             in
             buffer := buf;
             blocks := blks;
             Violet_surface.Parser.parse_buffer ~filename:module_file buf
           end
           else Violet_surface.Parser.parse_buffer ~filename d.text
         in
         let deps = Hashtbl.create 16 in
         let mods = Hashtbl.create 16 in
         Violet_project.Loader.prepare_dependencies
           ~text_override
           mode
           []
           mods
           deps
           (Violet_project.Loader.module_name module_file)
           m;
         match Tsort.sort @@ List.of_seq @@ Hashtbl.to_seq deps with
         | Sorted r ->
           List.iter
             (fun mn ->
                let mp = Violet_kernel.Syntax.Name.to_segments mn in
                Elab.check_module ~on_event ~module_path:mp (Hashtbl.find mods mn))
             r
         | ErrorCycle _ -> ())
     with
     | Exit -> ());
    let new_index = Violet_interactive.Collector.to_index collector in
    (* [to_scrbl] re-anchors a range onto the scrbl so the editor
       sees its own coordinates. Identity for a plain [.vt] (no blocks) and for
       ranges that map nowhere (e.g. dependency files). *)
    let to_scrbl loc =
      Option.value ~default:loc
      @@ Violet_literate.Source.remap_range
           ~blocks:!blocks
           ~scrbl_path:filename
           ~scrbl_text:d.text
           ~module_file
           loc
    in
    let new_index =
      if is_scrbl filename
      then Violet_interactive.Index.map_ranges to_scrbl new_index
      else new_index
    in
    let prev_last_good = !(d.snapshot).last_good_index in
    let has_errors =
      !aborted || Violet_common.Diagnostic_collector.has_errors diag_collector
    in
    let last_good = if has_errors then prev_last_good else new_index in
    let lsp_diags =
      Violet_common.Diagnostic_collector.all diag_collector
      |> List.map (fun (diag : Violet_common.Reporter.Message.t Asai.Diagnostic.t) ->
        let loc = Option.map to_scrbl diag.explanation.loc in
        Diagnostics.lsp_of_asai
          ~text:d.text
          { diag with explanation = { diag.explanation with loc } })
    in
    d.snapshot
    := { module_path
       ; diagnostics = lsp_diags
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

(* The literate-card tests below use fixed [.vt.scrbl] URIs that are never
   actually read from disk (the LSP drives elaboration off the in-memory
   buffer via [text_override]) — except now [recheck] also needs to resolve a
   project's [\literate] rule for `.scrbl`, which does require a real
   [info.vt] on disk somewhere above the URI's directory. That directory must
   be its own fixed subdirectory, not bare [/tmp]: other tests here construct
   unrelated fake paths directly under [/tmp] (e.g. [/tmp/Broken.vt]) and
   must NOT suddenly resolve into a project via ancestor search. *)
let scrbl_test_root = "/tmp/violet_checker_scrbl_test"

let ensure_scrbl_test_manifest () =
  if not (Sys.file_exists scrbl_test_root) then Unix.mkdir scrbl_test_root 0o755;
  let oc = open_out (Filename.concat scrbl_test_root "info.vt") in
  output_string
    oc
    "\\name \"checker-test\"\n\
     \\version \"0.1.0\"\n\
     \\literate \".scrbl\" (open = \"@vt|{\", close = \"}|\", output = \"cat\")\n";
  close_out oc
;;

let () = ensure_scrbl_test_manifest ()

let%expect_test "recheck of a literate card checks its @vt blocks" =
  let store = Doc_store.create () in
  let project_index = Project_index.create () in
  let uri =
    Linol_lsp.Lsp.Types.DocumentUri.of_path
      (Filename.concat scrbl_test_root "Card.vt.scrbl")
  in
  let text =
    {vt|@title{Demo}

@p{Prose around the code; the scanner must elaborate only the block.}

@vt|{
\universe U
\let f (A : U) : U => A
}|
|vt}
  in
  let _ = Doc_store.update store ~uri ~text ~version:1 in
  let c = create ~store ~project_index in
  recheck c ~uri;
  let snap = !((Option.get (Doc_store.find store ~uri)).snapshot) in
  let has_entries = List.length (Violet_interactive.Index.all_entries snap.index) > 0 in
  Printf.printf "diags=%d has_entries=%b" (List.length snap.diagnostics) has_entries;
  [%expect
    {|
    +checking [module] Card (/tmp/violet_checker_scrbl_test/Card.vt)
    diags=0 has_entries=true
    |}]
;;

let%expect_test "literate diagnostics are remapped onto the scrbl, not the buffer" =
  let store = Doc_store.create () in
  let project_index = Project_index.create () in
  let uri =
    Linol_lsp.Lsp.Types.DocumentUri.of_path
      (Filename.concat scrbl_test_root "Bad.vt.scrbl")
  in
  let text =
    {vt|@title{Bad}

@p{One.}
@p{Two.}

@vt|{
\universe U
\let bad : U => undefined_name
}|
|vt}
  in
  let _ = Doc_store.update store ~uri ~text ~version:1 in
  let c = create ~store ~project_index in
  recheck c ~uri;
  let snap = !((Option.get (Doc_store.find store ~uri)).snapshot) in
  let line0 =
    match snap.diagnostics with
    | diag :: _ -> diag.Linol_lsp.Lsp.Types.Diagnostic.range.start.line
    | [] -> -1
  in
  Printf.printf "diags=%d line0=%d" (List.length snap.diagnostics) line0;
  [%expect
    {|
    +checking [module] Bad (/tmp/violet_checker_scrbl_test/Bad.vt)
    diags=1 line0=7
    |}]
;;

let%expect_test "literate index is anchored to scrbl coordinates" =
  let store = Doc_store.create () in
  let project_index = Project_index.create () in
  let scrbl = Filename.concat scrbl_test_root "Card2.vt.scrbl" in
  let uri = Linol_lsp.Lsp.Types.DocumentUri.of_path scrbl in
  let text =
    {vt|@title{Demo}

@p{Prose.}

@vt|{
\universe U
\let f (A : U) : U => A
}|
|vt}
  in
  let _ = Doc_store.update store ~uri ~text ~version:1 in
  let c = create ~store ~project_index in
  recheck c ~uri;
  let idx = !((Option.get (Doc_store.find store ~uri)).snapshot).index in
  (match Violet_interactive.Index.find_at ~source:scrbl ~line:7 ~col:5 idx with
   | Some e ->
     let path = Violet_kernel.Syntax.Name.of_segments e.Violet_interactive.Index.path in
     let def_line =
       match e.Violet_interactive.Index.def_target with
       | Some loc ->
         (match Asai.Range.split loc with
          | s, _ -> s.Asai.Range.line_num
          | exception _ -> -1)
       | None -> -1
     in
     Printf.printf "path=%s def_line=%d" path def_line
   | None -> Printf.printf "no hit");
  [%expect
    {|
    +checking [module] Card2 (/tmp/violet_checker_scrbl_test/Card2.vt)
    path=f def_line=7
    |}]
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

let%expect_test "recheck continues after first error and collects multiple diagnostics" =
  let store = Doc_store.create () in
  let project_index = Project_index.create () in
  let uri = Linol_lsp.Lsp.Types.DocumentUri.of_path "/tmp/Multi.vt" in
  let text =
    {|\universe U
\let bad1 : U => not_defined
\let good (A : U) : U => A
\let bad2 : U => also_not_defined
|}
  in
  let _ = Doc_store.update store ~uri ~text ~version:1 in
  let c = create ~store ~project_index in
  recheck c ~uri;
  let d = Option.get (Doc_store.find store ~uri) in
  let snap = !(d.snapshot) in
  let entry_count = List.length (Violet_interactive.Index.all_entries snap.index) in
  Printf.printf "diags=%d entries=%d" (List.length snap.diagnostics) entry_count;
  [%expect
    {|
    +checking [module] Multi (/tmp/Multi.vt)
    diags=2 entries=9
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
