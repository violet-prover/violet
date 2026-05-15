(* Baseline regression test for example/*.vt.

   Each example is run in a forked subprocess with a SIGALRM-based timeout.
   We compare actual outcome (OK / FAIL / HUNG) against the recorded
   expectations below.  This lets us detect both improvement *and* regression
   during refactors.

   When the refactor lands and an example starts behaving differently, update
   `expected` to match — that's the point.  Don't paper over the diff. *)

type outcome =
  [ `Ok
  | `Fail
  | `Hung
  ]

let timeout_sec = 30

(* Topologically load the file and its imports, mirroring what bin/main.ml's
   `prepare_dependencies` does. Without this, examples that `import nat` fail
   to find Nat / zero / suc when checked alone. *)
let load_with_deps (filename : string) : Violet_elab.Surface.t list =
  let mods = Hashtbl.create 16 in
  let deps = Hashtbl.create 16 in
  let rec walk m =
    let key = Filename.chop_extension @@ Filename.basename m.Violet_elab.Surface.name in
    if Hashtbl.mem deps key
    then ()
    else begin
      Hashtbl.add mods key m;
      let values = List.map (fun path -> String.concat "." path) m.imports in
      Hashtbl.add deps key values;
      List.iter
        (fun library ->
           let filepath =
             Filename.dirname m.name ^ "/" ^ String.concat "/" library ^ ".vt"
           in
           walk (Violet_elab.Parser.parse_file filepath))
        m.imports
    end
  in
  walk (Violet_elab.Parser.parse_file filename);
  match Tsort.sort @@ List.of_seq @@ Hashtbl.to_seq deps with
  | Sorted r -> List.map (Hashtbl.find mods) r
  | ErrorCycle _ -> failwith "import cycle"
;;

let run_check_in_child filename =
  let devnull = Unix.openfile "/dev/null" [ Unix.O_WRONLY ] 0 in
  Unix.dup2 devnull Unix.stdout;
  Unix.dup2 devnull Unix.stderr;
  Unix.close devnull;
  let exit_code = ref 0 in
  (try
     Eio_main.run
     @@ fun _env ->
     Violet_elab.Reporter.run ~emit:(fun _ -> ()) ~fatal:(fun _ -> exit 1)
     @@ fun () ->
     let open Violet_elab.Context.Handler in
     Violet_elab.Context.S.run ~shadow ~not_found ~hook
     @@ fun () ->
     let open Violet_elab.Env.Handler in
     Violet_elab.Env.S.run ~shadow ~not_found ~hook
     @@ fun () -> List.iter Violet_elab.Elab.check_module (load_with_deps filename)
   with
   | _ -> exit_code := 1);
  exit !exit_code
;;

let outcome_of filename : outcome =
  flush stdout;
  match Unix.fork () with
  | 0 -> run_check_in_child filename
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
     | _ -> `Fail)
;;

let outcome_str = function
  | `Ok -> "OK"
  | `Fail -> "FAIL"
  | `Hung -> "HUNG"
;;

(* Current behaviour of each example under the existing elaborator.
   Refactor goal is to keep OK/OK working, and (eventually) push the FAIL/HUNG
   entries toward OK as unification improves. *)
let expected : (string * outcome) list =
  [ "../example/bool.vt", `Ok
  ; "../example/nat.vt", `Ok
  ; "../example/list.vt", `Ok
  ; "../example/vec.vt", `Ok
  ; "../example/equality.vt", `Ok
  ; "../example/index.vt", `Ok
  ; "../example/nat-properties.vt", `Ok
  ; "../example/compute.vt", `Ok
  ; "../example/universe-explicit.vt", `Ok
  ; "../example/sigma.vt", `Ok
  ; "../example/sigma-multi.vt", `Ok
  ; "../example/ind-namespacing.vt", `Ok
  ; "../example/pterodactyl.vt", `Ok
  ; "../example/bad/bad-stack-not-pi.vt", `Fail
  ; "../example/bad/bad-stack-coverage.vt", `Fail
  ; "../example/bad/independent-universes-bad.vt", `Fail
  ; "../example/bad/bad-positivity-negative.vt", `Fail
  ; "../example/bad/bad-positivity-nested.vt", `Fail
  ; "../example/bad/bad-positivity-non-uniform.vt", `Fail
  ]
;;

let () =
  let mismatches = ref 0 in
  List.iter
    (fun (filename, want) ->
       let got = outcome_of filename in
       if got = want
       then Printf.printf "%s: %s (as expected)\n" filename (outcome_str got)
       else begin
         Printf.printf
           "%s: got %s, expected %s\n"
           filename
           (outcome_str got)
           (outcome_str want);
         incr mismatches
       end)
    expected;
  if !mismatches > 0
  then begin
    Printf.printf "\n%d mismatch(es)\n" !mismatches;
    exit 1
  end
;;
