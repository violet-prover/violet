open Cmdliner
open Cli_common

let cmd ~env =
  let doc = "Start language server (LSP over stdio)" in
  let info = Cmd.info "lsp" ~version ~doc in
  let arg_stdio =
    Arg.value @@ Arg.flag @@ Arg.info [ "stdio" ] ~doc:"Use stdio transport (default)"
  in
  let run _enable_stdio = Violet_langserver.Server.run ~env () in
  Cmd.v info Term.(const run $ arg_stdio)
;;
