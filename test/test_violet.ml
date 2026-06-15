(* Baseline regression test for the .vt fixture corpus.

   This harness AUTO-DISCOVERS the .vt corpus rather than hand-listing each
   fixture. Each fixture is run in a forked subprocess with a SIGALRM-based
   timeout and a per-fixture temp file that the child writes its diagnostic
   explanation to on fatal error. The discovered outcome is one of:

   - `Ok       — successful elaboration.
   - `Fail msg — failure; `msg` is the rendered diagnostic explanation.
   - `Hung     — exceeded `timeout_sec`.

   Discovery rules:
   - Files under test/fixtures/src/ and ../example/src/ must elaborate Ok.
   - Files under test/fixtures/bad/ must FAIL, and the rendered explanation
     must byte-equal a committed golden `<fixture>.vt.expected` file.
   - Files under test/fixtures/goal/ must elaborate (unresolved goals are
     warnings, not errors), and the rendered GOAL REPORTS — every `?hole`'s
     context + target display, in elaboration order — must byte-equal a
     committed golden `<fixture>.vt.expected` file. These pin the
     pretty-printer's behavior (operator notation, eliminator folding) across
     real-world proof contexts.
   - Companion modules whose basename starts with `_` are imported by other
     fixtures and are NOT run as standalone entries (skipped in discovery).

   To regenerate the golden files after an intentional message change, run
   the test exe with the env var PROMOTE_GOLDENS=1 set. *)

type outcome =
  [ `Ok
  | `Ok_with of string (* successful elaboration + collected goal reports *)
  | `Fail of string
  | `Hung
  ]

type want =
  [ `Ok
  | `Hung
  ]

let timeout_sec = 30

(* Topologically load the file and its imports, mirroring what bin/main.ml's
   `prepare_dependencies` does. Without this, examples that `import nat` fail
   to find Nat / zero / suc when checked alone. *)
let load_with_deps (filename : string) : (string * Violet_surface.Surface.t) list =
  let mods = Hashtbl.create 16 in
  let deps = Hashtbl.create 16 in
  let mode =
    match Violet_project.Root.find_root (Filename.dirname filename) with
    | Some root ->
      (try `Project (Violet_project.Resolve.load root) with
       | Violet_project.Resolve.Project_error msg -> failwith msg)
    | None -> `Single_file (Filename.dirname filename)
  in
  (* `prefix_segs` are the canonical module-path segments above the file
     currently being walked. Each child's canonical key is
     `prefix_segs @ user_import`; the prefix grows by the crossed dep_key
     whenever an import crosses into a dep. Both the mods hashtable and the
     deps adjacency list use canonical keys, and the Surface.t stored in mods
     has its `imports` field rewritten to canonical paths so the elaborator's
     `renaming` finds the imported module's section. *)
  let rec walk ctx prefix_segs key m =
    if Hashtbl.mem deps key
    then ()
    else begin
      let canonical_libraries =
        List.map (fun lib -> prefix_segs @ lib) m.Violet_surface.Surface.imports
      in
      Hashtbl.add mods key { m with Violet_surface.Surface.imports = canonical_libraries };
      Hashtbl.add deps key (List.map (String.concat "/") canonical_libraries);
      List.iter2
        (fun user_library canonical_library ->
           let canonical_key = String.concat "/" canonical_library in
           let next_ctx, next_segs, filepath =
             match ctx with
             | `Project proj ->
               let p, crossed, fp =
                 Violet_project.Resolve.resolve_import_in proj user_library
               in
               let ns =
                 match crossed with
                 | Some k -> prefix_segs @ [ k ]
                 | None -> prefix_segs
               in
               `Project p, ns, fp
             | `Single_file root ->
               ctx, prefix_segs, root ^ "/" ^ String.concat "/" user_library ^ ".vt"
           in
           walk
             next_ctx
             next_segs
             canonical_key
             (Violet_surface.Parser.parse_file filepath))
        m.imports
        canonical_libraries
    end
  in
  let m = Violet_surface.Parser.parse_file filename in
  let root_key = Filename.chop_extension @@ Filename.basename m.name in
  walk mode [] root_key m;
  match Tsort.sort @@ List.of_seq @@ Hashtbl.to_seq deps with
  | Sorted r -> List.map (fun k -> k, Hashtbl.find mods k) r
  | ErrorCycle _ -> failwith "import cycle"
;;

(* Render a diagnostic's source span as `line:col-line:col` so that the
   bad/ goldens pin error POSITIONS, not just messages. Columns are 1-based. *)
let render_loc : Asai.Range.t option -> string = function
  | None -> "<no location>"
  | Some r ->
    (match Asai.Range.view r with
     | `Range (s, e) ->
       Printf.sprintf
         "%d:%d-%d:%d"
         s.Asai.Range.line_num
         (s.Asai.Range.offset - s.Asai.Range.start_of_line + 1)
         e.Asai.Range.line_num
         (e.Asai.Range.offset - e.Asai.Range.start_of_line + 1)
     | `End_of_file p ->
       Printf.sprintf
         "eof %d:%d"
         p.Asai.Range.line_num
         (p.Asai.Range.offset - p.Asai.Range.start_of_line + 1))
;;

(* In the child: silence stdout/stderr (to keep the test log clean), then
   run the elaborator. On fatal error, render the diagnostic's explanation
   to `msg_file` and exit 1. With [goals] and no error, write every rendered
   Goal_report to `msg_file` instead (still exit 0). The parent reads
   `msg_file` after waitpid. *)
let run_check_in_child ?(goals = false) filename ~msg_file =
  let devnull = Unix.openfile "/dev/null" [ Unix.O_WRONLY ] 0 in
  Unix.dup2 devnull Unix.stdout;
  Unix.dup2 devnull Unix.stderr;
  Unix.close devnull;
  let exit_code = ref 0 in
  let diag_collector = Violet_common.Diagnostic_collector.create () in
  let emit d = Violet_common.Diagnostic_collector.emit diag_collector d in
  let fatal d =
    emit d;
    exit_code := 1;
    raise Exit
  in
  (try
     Eio_main.run
     @@ fun _env ->
     Violet_common.Reporter.run ~emit ~fatal
     @@ fun () ->
     let open Violet_elab.Context.Handler in
     Violet_elab.Context.S.run ~shadow ~not_found ~hook
     @@ fun () ->
     let open Violet_elab.Env.Handler in
     Violet_elab.Env.S.run ~shadow ~not_found ~hook
     @@ fun () ->
     List.iter
       (fun (key, m) ->
          let module_path = String.split_on_char '/' key in
          Violet_elab.Elab.check_module ~module_path m)
       (load_with_deps filename)
   with
   | _ -> ());
  (match Violet_common.Diagnostic_collector.latest_error diag_collector with
   | Some d ->
     exit_code := 1;
     (try
        let oc = open_out msg_file in
        output_string
          oc
          (render_loc d.explanation.loc
           ^ "\n"
           ^ Asai.Diagnostic.string_of_text d.explanation.value);
        close_out oc
      with
      | _ -> ())
   | None ->
     if goals
     then begin
       let reports =
         Violet_common.Diagnostic_collector.all diag_collector
         |> List.filter (fun (d : _ Asai.Diagnostic.t) ->
           match d.message with
           | Violet_common.Reporter.Message.Goal_report -> true
           | _ -> false)
         |> List.map (fun (d : _ Asai.Diagnostic.t) ->
           (* NOT string_of_text — that replaces the report's newlines with
              spaces, flattening the context/target layout the golden pins. *)
           render_loc d.explanation.loc ^ "\n" ^ Format.asprintf "%t" d.explanation.value)
       in
       try
         let oc = open_out msg_file in
         output_string oc (String.concat "\n\n" reports);
         close_out oc
       with
       | _ -> ()
     end);
  exit !exit_code
;;

let read_msg_file path : string =
  try
    let ic = open_in path in
    let n = in_channel_length ic in
    let buf = Bytes.create n in
    really_input ic buf 0 n;
    close_in ic;
    Bytes.to_string buf
  with
  | _ -> ""
;;

let outcome_of ?(goals = false) filename : outcome =
  let msg_file = Filename.temp_file "violet-test-" ".txt" in
  flush stdout;
  let result =
    match Unix.fork () with
    | 0 -> run_check_in_child ~goals filename ~msg_file
    | pid ->
      let prev_handler =
        Sys.signal
          Sys.sigalrm
          (Sys.Signal_handle
             (fun _ ->
               try Unix.kill pid Sys.sigkill with
               | _ -> ()))
      in
      let _ = Unix.alarm timeout_sec in
      let rec wait () =
        try snd (Unix.waitpid [] pid) with
        | Unix.Unix_error (Unix.EINTR, _, _) -> wait ()
      in
      let status = wait () in
      let _ = Unix.alarm 0 in
      Sys.set_signal Sys.sigalrm prev_handler;
      (match status with
       | Unix.WEXITED 0 -> if goals then `Ok_with (read_msg_file msg_file) else `Ok
       | Unix.WSIGNALED s when s = Sys.sigkill -> `Hung
       | _ -> `Fail (read_msg_file msg_file))
  in
  (try Unix.unlink msg_file with
   | _ -> ());
  result
;;

let outcome_str = function
  | `Ok -> "OK"
  | `Ok_with _ -> "OK"
  | `Fail _ -> "FAIL"
  | `Hung -> "HUNG"
;;

let want_str = function
  | `Ok -> "OK"
  | `Hung -> "HUNG"
;;

(* Auto-discovery of the .vt corpus.

   - fixtures/src and example/src must elaborate Ok.
   - fixtures/bad must FAIL, and the rendered diagnostic must byte-equal a
     committed golden file `<fixture>.vt.expected`.

   Companion modules exist only to be imported by another fixture (e.g. the
   importer fixtures that test cross-module visibility); they are skipped as
   standalone test entries — a valid companion in bad/ would otherwise fail the
   "must FAIL" check. They are listed explicitly by basename rather than marked
   with a filename prefix, because a Violet import path cannot begin with `_`. *)
let companion_modules = [ "exportlib.vt" ]

let vt_entries (dir : string) : string list =
  Sys.readdir dir
  |> Array.to_list
  |> List.filter (fun f ->
    Filename.check_suffix f ".vt" && not (List.mem f companion_modules))
  |> List.sort String.compare
  |> List.map (fun f -> Filename.concat dir f)
;;

(* The only outcome that cannot be inferred from the directory: fixtures we
   expect to exceed the timeout. Keyed by the path as discovered. *)
let hung_overrides : string list = []
let golden_path vt = vt ^ ".expected"
let read_file = read_msg_file

(* Literate (weave) corpus: [*.vt.scrbl] cards under fixtures/literate/bad must
   FAIL the literate scanner (e.g. an unterminated [@vt|{] block), and the
   rendered diagnostic must byte-equal a committed golden, exactly like the
   bad/ corpus. We drive [Block.scan] directly under a collecting reporter
   rather than through the fork harness: scanning cannot hang, and this keeps
   the golden free of project-resolution noise. *)
let scrbl_entries (dir : string) : string list =
  if Sys.file_exists dir
  then
    Sys.readdir dir
    |> Array.to_list
    |> List.filter (fun f -> Filename.check_suffix f ".vt.scrbl")
    |> List.sort String.compare
    |> List.map (fun f -> Filename.concat dir f)
  else []
;;

let literate_outcome (scrbl : string) : [ `Ok | `Fail of string ] =
  let text = read_file scrbl in
  let diag = Violet_common.Diagnostic_collector.create () in
  let emit d = Violet_common.Diagnostic_collector.emit diag d in
  (try
     Violet_common.Reporter.run
       ~emit
       ~fatal:(fun d ->
         emit d;
         raise Exit)
       (fun () -> ignore (Violet_literate.Block.scan ~source:scrbl text))
   with
   | Exit -> ());
  match Violet_common.Diagnostic_collector.latest_error diag with
  | Some d ->
    `Fail
      (render_loc d.explanation.loc
       ^ "\n"
       ^ Asai.Diagnostic.string_of_text d.explanation.value)
  | None -> `Ok
;;

(* Outcome comparison for the Ok/Hung (src/example) path. bad/ fixtures are
   compared against golden files instead, so they don't go through this. *)
type cmp =
  [ `Match
  | `Mismatch_outcome
  ]

let compare_outcome (got : outcome) (want : want) : cmp =
  match got, want with
  | `Ok, `Ok -> `Match
  | `Hung, `Hung -> `Match
  | _ -> `Mismatch_outcome
;;

let () =
  let mismatches = ref 0 in
  let promote = Option.is_some (Sys.getenv_opt "PROMOTE_GOLDENS") in
  (* src/ and example/ must elaborate Ok (unless overridden to Hung). *)
  let oks = vt_entries "./fixtures/src" @ vt_entries "../example/src" in
  List.iter
    (fun vt ->
       let got = outcome_of vt in
       let want = if List.mem vt hung_overrides then `Hung else `Ok in
       match compare_outcome got want with
       | `Match -> Printf.printf "%s: %s (as expected)\n" vt (outcome_str got)
       | `Mismatch_outcome ->
         Printf.printf "%s: got %s, expected %s\n" vt (outcome_str got) (want_str want);
         incr mismatches)
    oks;
  (* bad/ must FAIL, and the rendered message must match the committed golden. *)
  let bads = vt_entries "./fixtures/bad" in
  List.iter
    (fun vt ->
       match outcome_of vt with
       | `Ok | `Ok_with _ ->
         Printf.printf "%s: got OK, expected FAIL\n" vt;
         incr mismatches
       | `Hung ->
         Printf.printf "%s: got HUNG, expected FAIL\n" vt;
         incr mismatches
       | `Fail msg ->
         let msg = String.trim msg in
         if promote
         then begin
           let oc = open_out (golden_path vt) in
           output_string oc (msg ^ "\n");
           close_out oc;
           Printf.printf "%s: golden written\n" vt
         end
         else begin
           let want =
             String.trim
               (try read_file (golden_path vt) with
                | _ -> "")
           in
           if String.equal msg want
           then Printf.printf "%s: FAIL (golden matches)\n" vt
           else begin
             Printf.printf
               "%s: golden mismatch\n--- want ---\n%s\n--- got ---\n%s\n"
               vt
               want
               msg;
             incr mismatches
           end
         end)
    bads;
  (* literate/bad: [*.vt.scrbl] cards that must FAIL the literate scanner,
     compared against a committed golden in the bad/ format. *)
  let literate_bads = scrbl_entries "./fixtures/literate/bad" in
  List.iter
    (fun scrbl ->
       match literate_outcome scrbl with
       | `Ok ->
         Printf.printf "%s: got OK, expected FAIL\n" scrbl;
         incr mismatches
       | `Fail msg ->
         let msg = String.trim msg in
         if promote
         then begin
           let oc = open_out (golden_path scrbl) in
           output_string oc (msg ^ "\n");
           close_out oc;
           Printf.printf "%s: golden written\n" scrbl
         end
         else begin
           let want =
             String.trim
               (try read_file (golden_path scrbl) with
                | _ -> "")
           in
           if String.equal msg want
           then Printf.printf "%s: FAIL (golden matches)\n" scrbl
           else begin
             Printf.printf
               "%s: golden mismatch\n--- want ---\n%s\n--- got ---\n%s\n"
               scrbl
               want
               msg;
             incr mismatches
           end
         end)
    literate_bads;
  (* goal/ must elaborate (unresolved goals are warnings), and the rendered
     goal reports must match the committed golden — these pin the pretty
     printer (operator notation, eliminator folding) across real contexts. *)
  let goal_entries =
    if Sys.file_exists "./fixtures/goal" then vt_entries "./fixtures/goal" else []
  in
  List.iter
    (fun vt ->
       match outcome_of ~goals:true vt with
       | `Hung ->
         Printf.printf "%s: got HUNG, expected goal reports\n" vt;
         incr mismatches
       | `Fail msg ->
         Printf.printf "%s: got FAIL, expected goal reports\n--- error ---\n%s\n" vt msg;
         incr mismatches
       | `Ok ->
         (* unreachable: ~goals:true always returns `Ok_with on success *)
         Printf.printf "%s: unexpected bare OK in goal mode\n" vt;
         incr mismatches
       | `Ok_with msg ->
         let msg = String.trim msg in
         if promote
         then begin
           let oc = open_out (golden_path vt) in
           output_string oc (msg ^ "\n");
           close_out oc;
           Printf.printf "%s: golden written\n" vt
         end
         else begin
           let want =
             String.trim
               (try read_file (golden_path vt) with
                | _ -> "")
           in
           if String.equal msg want
           then Printf.printf "%s: OK (goal reports match)\n" vt
           else begin
             Printf.printf
               "%s: goal-report mismatch\n--- want ---\n%s\n--- got ---\n%s\n"
               vt
               want
               msg;
             incr mismatches
           end
         end)
    goal_entries;
  if !mismatches > 0
  then begin
    Printf.printf "\n%d mismatch(es)\n" !mismatches;
    exit 1
  end
;;
