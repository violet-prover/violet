(* Run a project's [\literate <ext> (..., output = "cmd")] command over one
   rendered code block. Violet has no built-in notion of any output format
   ([weave-output-hook-design.md] §2) — the command decides how (or whether)
   to embed the highlighted HTML fragment into the target document; its
   stdout is spliced back verbatim in place of the block. *)

let run ~(cmd : string) (html : string) : string =
  let stdout, stdin = Unix.open_process cmd in
  output_string stdin html;
  close_out stdin;
  let output = In_channel.input_all stdout in
  match Unix.close_process (stdout, stdin) with
  | Unix.WEXITED 0 -> output
  | Unix.WEXITED code ->
    Violet_common.Reporter.fatalf
      Parse_error
      "output hook `%s` exited with code %d"
      cmd
      code
  | Unix.WSIGNALED s | Unix.WSTOPPED s ->
    Violet_common.Reporter.fatalf
      Parse_error
      "output hook `%s` was killed by signal %d"
      cmd
      s
;;

let%expect_test "run pipes stdin through the command and returns stdout" =
  print_string (run ~cmd:"cat" "hello");
  [%expect {| hello |}]
;;

let%expect_test "run applies a transforming command" =
  print_string (run ~cmd:"sed 's/x/y/g'" "xxx");
  [%expect {| yyy |}]
;;

let%expect_test "run reports a non-zero exit as a fatal diagnostic" =
  Violet_common.Reporter.run
    ~emit:(fun _ -> ())
    ~fatal:(fun d -> Format.printf "%t@." d.Asai.Diagnostic.explanation.value)
    (fun () -> ignore (run ~cmd:"sh -c 'exit 3'" "x"));
  [%expect {| output hook `sh -c 'exit 3'` exited with code 3 |}]
;;
