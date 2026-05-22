(* Baseline regression test for the .vt fixture corpus.

   Each fixture is run in a forked subprocess with a SIGALRM-based timeout
   and a per-fixture temp file that the child writes its diagnostic
   explanation to on fatal error.  We compare the actual outcome
   (`Ok / `Fail msg / `Hung) against a `want` annotation:

   - `Ok            — expect successful elaboration.
   - `Fail          — expect any failure (legacy; new entries should
                      use `FailWith to pin the cause).
   - `FailWith subs — expect failure whose explanation contains EVERY
                      substring in `subs`. Use [single_phrase] for the
                      common one-substring case; multi-substring is for
                      pinning category+context (e.g. "duplicate field"
                      AND "record update").
   - `Hung          — expect to exceed `timeout_sec`.

   When a refactor lands and a fixture behaves differently, update the
   annotation to match — that's the point.  Don't paper over the diff. *)

type outcome =
  [ `Ok
  | `Fail of string
  | `Hung
  ]

type want =
  [ `Ok
  | `Fail
  | `FailWith of string list
  | `Hung
  ]

let timeout_sec = 30

(* Topologically load the file and its imports, mirroring what bin/main.ml's
   `prepare_dependencies` does. Without this, examples that `import nat` fail
   to find Nat / zero / suc when checked alone. *)
let load_with_deps (filename : string) : (string * Violet_elab.Surface.t) list =
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
        List.map (fun lib -> prefix_segs @ lib) m.Violet_elab.Surface.imports
      in
      Hashtbl.add mods key { m with Violet_elab.Surface.imports = canonical_libraries };
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
           walk next_ctx next_segs canonical_key (Violet_elab.Parser.parse_file filepath))
        m.imports
        canonical_libraries
    end
  in
  let m = Violet_elab.Parser.parse_file filename in
  let root_key = Filename.chop_extension @@ Filename.basename m.name in
  walk mode [] root_key m;
  match Tsort.sort @@ List.of_seq @@ Hashtbl.to_seq deps with
  | Sorted r -> List.map (fun k -> k, Hashtbl.find mods k) r
  | ErrorCycle _ -> failwith "import cycle"
;;

(* In the child: silence stdout/stderr (to keep the test log clean), then
   run the elaborator. On fatal error, render the diagnostic's explanation
   to `msg_file` and exit 1. The parent reads `msg_file` after waitpid. *)
let run_check_in_child filename ~msg_file =
  let devnull = Unix.openfile "/dev/null" [ Unix.O_WRONLY ] 0 in
  Unix.dup2 devnull Unix.stdout;
  Unix.dup2 devnull Unix.stderr;
  Unix.close devnull;
  let exit_code = ref 0 in
  (try
     Eio_main.run
     @@ fun _env ->
     Violet_elab.Reporter.run
       ~emit:(fun _ -> ())
       ~fatal:(fun (d : Violet_elab.Reporter.Message.t Asai.Diagnostic.t) ->
         (try
            let oc = open_out msg_file in
            output_string oc (Asai.Diagnostic.string_of_text d.explanation.value);
            close_out oc
          with
          | _ -> ());
         exit 1)
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
   | _ -> exit_code := 1);
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

let outcome_of filename : outcome =
  let msg_file = Filename.temp_file "violet-test-" ".txt" in
  flush stdout;
  let result =
    match Unix.fork () with
    | 0 -> run_check_in_child filename ~msg_file
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
       | Unix.WEXITED 0 -> `Ok
       | Unix.WSIGNALED s when s = Sys.sigkill -> `Hung
       | _ -> `Fail (read_msg_file msg_file))
  in
  (try Unix.unlink msg_file with
   | _ -> ());
  result
;;

let outcome_str = function
  | `Ok -> "OK"
  | `Fail _ -> "FAIL"
  | `Hung -> "HUNG"
;;

let want_str = function
  | `Ok -> "OK"
  | `Fail -> "FAIL"
  | `FailWith subs -> Printf.sprintf "FAIL/%s" (String.concat " ⊕ " subs)
  | `Hung -> "HUNG"
;;

(* Result of comparing actual against expected. The `Mismatch payload
   records what went wrong so the run loop can print a useful diff. *)
type cmp =
  [ `Match
  | `Mismatch_outcome
  | `Missing_substring of string * string (* expected sub, actual msg *)
  ]

let contains haystack needle =
  let lh = String.length haystack
  and ln = String.length needle in
  if ln = 0
  then true
  else (
    let rec scan i =
      if i + ln > lh
      then false
      else if String.sub haystack i ln = needle
      then true
      else scan (i + 1)
    in
    scan 0)
;;

let compare_outcome (got : outcome) (want : want) : cmp =
  match got, want with
  | `Ok, `Ok -> `Match
  | `Hung, `Hung -> `Match
  | `Fail _, `Fail -> `Match
  | `Fail msg, `FailWith subs ->
    (match List.find_opt (fun s -> not (contains msg s)) subs with
     | None -> `Match
     | Some missing -> `Missing_substring (missing, msg))
  | _ -> `Mismatch_outcome
;;

let expected : (string * want) list =
  [ "../example/src/index.vt", `Ok
  ; "../example/src/pterodactyl.vt", `Ok
  ; "../example/src/operators.vt", `Ok
  ; "../example/src/record.vt", `Ok
  ; "./fixtures/src/compute.vt", `Ok
  ; "./fixtures/src/universe-explicit.vt", `Ok
  ; "./fixtures/src/ind-namespacing.vt", `Ok
  ; "./fixtures/src/operators-user.vt", `Ok
  ; "./fixtures/src/goal_demo.vt", `Ok
  ; "./fixtures/bad/bad-stack-not-pi.vt", `FailWith [ "needs a function type" ]
  ; "./fixtures/bad/bad-stack-coverage.vt", `FailWith [ "no clause for constructor" ]
  ; "./fixtures/src/stack-machine.vt", `Ok
  ; ( "./fixtures/bad/independent-universes-bad.vt"
    , `FailWith [ "cannot unify"; "universe" ] )
  ; "./fixtures/bad/bad-positivity-negative.vt", `FailWith [ "negative position" ]
  ; "./fixtures/bad/bad-positivity-nested.vt", `FailWith [ "non-positive slot" ]
  ; "./fixtures/bad/bad-positivity-non-uniform.vt", `FailWith [ "non-uniformly" ]
  ; ( "./fixtures/bad/bad-operator-no-holes.vt"
    , `FailWith [ "template must contain at least one hole" ] )
  ; ( "./fixtures/bad/bad-operator-duplicate.vt"
    , `FailWith [ "duplicate operator template" ] )
  ; "./fixtures/bad/bad-operator-cycle.vt", `FailWith [ "precedence cycle" ]
  ; "./fixtures/src/record-extras.vt", `Ok
  ; "./fixtures/src/record-eta.vt", `Ok
  ; ( "./fixtures/bad/bad-record-missing-field.vt"
    , `FailWith [ "missing field"; "record literal" ] )
  ; "./fixtures/bad/bad-proj-unknown-field.vt", `FailWith [ "has no field" ]
  ; ( "./fixtures/bad/bad-proj-non-record.vt"
    , `FailWith [ "expected a record type for projection" ] )
  ; ( "./fixtures/bad/bad-record-update-unknown-field.vt"
    , `FailWith [ "unknown field"; "record update" ] )
  ; "./fixtures/bad/bad-record-update-empty.vt", `FailWith [ "empty record update" ]
  ; ( "./fixtures/bad/bad-record-pattern-missing-field.vt"
    , `FailWith [ "missing field"; "record pattern" ] )
  ; ( "./fixtures/bad/bad-record-pattern-unknown-field.vt"
    , `FailWith [ "unknown field"; "record pattern" ] )
  ; ( "./fixtures/bad/bad-record-duplicate-field.vt"
    , `FailWith [ "duplicate field"; "record literal" ] )
  ; "./fixtures/src/dependent-record-literal.vt", `Ok
  ; "./fixtures/src/elim-unify.vt", `Ok
  ; "./fixtures/src/vec-head.vt", `Ok
  ; "./fixtures/bad/bad-elim-stuck.vt", `FailWith [ "unifier got stuck" ]
  ; ( "./fixtures/bad/bad-record-literal-unknown.vt"
    , `FailWith [ "unknown field"; "record literal" ] )
  ; ( "./fixtures/bad/bad-record-update-duplicate.vt"
    , `FailWith [ "duplicate field"; "record update" ] )
  ; "./fixtures/src/positivity-self-shadow.vt", `Ok
  ; "./fixtures/src/record-update-dep-chain.vt", `Ok
  ; "./fixtures/src/stress-pi-chain.vt", `Ok
  ; "./fixtures/src/stress-long-spine.vt", `Ok
  ; "./fixtures/src/stress-many-fields.vt", `Ok
  ; "./fixtures/src/stress-many-ctors.vt", `Ok
  ; "./fixtures/src/stress-deep-vec.vt", `Ok
  ; "./fixtures/src/stress-deep-nat.vt", `Ok
  ; "./fixtures/src/underscore-name.vt", `Ok
  ]
;;

let () =
  let mismatches = ref 0 in
  List.iter
    (fun (filename, want) ->
       let got = outcome_of filename in
       match compare_outcome got want with
       | `Match -> Printf.printf "%s: %s (as expected)\n" filename (outcome_str got)
       | `Mismatch_outcome ->
         Printf.printf
           "%s: got %s, expected %s\n"
           filename
           (outcome_str got)
           (want_str want);
         incr mismatches
       | `Missing_substring (sub, msg) ->
         Printf.printf
           "%s: FAIL but explanation did not contain %S\n  actual: %s\n"
           filename
           sub
           msg;
         incr mismatches)
    expected;
  if !mismatches > 0
  then begin
    Printf.printf "\n%d mismatch(es)\n" !mismatches;
    exit 1
  end
;;
