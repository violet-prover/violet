open Cmdliner
module Tty = Asai.Tty.Make (Violet.Reporter.Message)

let version = "0.1.0"

let load_cmd ~env =
  let _ = env in
  let arg_file =
    let doc = "The program file to load." in
    Arg.required @@ Arg.pos 0 (Arg.some Arg.file) None @@ Arg.info [] ~docv:"PROG" ~doc
  in
  let doc = "Load input program file into REPL" in
  let man = [ `S Manpage.s_description; `P "" ] in
  let info = Cmd.info "load" ~version ~doc ~man in
  Cmd.v
    info
    Term.(
      const (fun filename ->
        let m = Violet.Parser.parse_file filename in
        Violet.Checker.check_module m;
        ())
      $ arg_file)
;;

let cmd ~env =
  let doc = "violet" in
  let man = [ `S Manpage.s_bugs; `S Manpage.s_authors; `P "Lîm Tsú-thuàn" ] in
  let info = Cmd.info "violet" ~version ~doc ~man in
  Cmd.group info [ load_cmd ~env ]
;;

let () =
  let fatal diagnostics =
    Tty.display diagnostics;
    exit 1
  in
  Printexc.record_backtrace true;
  Eio_main.run
  @@ fun env ->
  Violet.Reporter.run ~emit:Tty.display ~fatal
  @@ fun () ->
  let open Violet.Context.Handler in
  Violet.Context.S.run ~shadow ~not_found ~hook
  @@ fun () ->
  let open Violet.Env.Handler in
  Violet.Env.S.run ~shadow ~not_found ~hook
  @@ fun () -> exit @@ Cmd.eval ~catch:false @@ cmd ~env
;;
