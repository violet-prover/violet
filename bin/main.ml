open Cmdliner
module Tty = Asai.Tty.Make (Violet_surface.Reporter.Message)

let cmd ~env =
  let doc = "violet" in
  let man = [ `S Manpage.s_bugs; `S Manpage.s_authors; `P "Lîm Tsú-thuàn" ] in
  let info = Cmd.info "violet" ~version:Cli_common.version ~doc ~man in
  Cmd.group
    info
    [ Cmd_load.cmd ~env
    ; Cmd_check.cmd ~env
    ; Cmd_update.cmd ~env
    ; Cmd_new.cmd ~env
    ; Cmd_init.cmd ~env
    ; Cmd_add.cmd ~env
    ; Cmd_weave.cmd ~env
    ; Cmd_lsp.cmd ~env
    ]
;;

let () =
  let collector = Violet_common.Diagnostic_collector.create () in
  let emit diag =
    Violet_common.Diagnostic_collector.emit collector diag;
    Tty.display diag
  in
  let fatal diag =
    emit diag;
    exit 1
  in
  Printexc.record_backtrace true;
  Eio_main.run
  @@ fun env ->
  Violet_surface.Reporter.run ~emit ~fatal
  @@ fun () ->
  let open Violet_elab.Context.Handler in
  Violet_elab.Context.S.run ~shadow ~not_found ~hook
  @@ fun () ->
  let open Violet_elab.Env.Handler in
  Violet_elab.Env.S.run ~shadow ~not_found ~hook
  @@ fun () ->
  let code = Cmd.eval ~catch:false @@ cmd ~env in
  if Violet_common.Diagnostic_collector.has_errors collector then exit 1 else exit code
;;
