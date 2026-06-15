open Cmdliner
open Cli_common

let new_ project =
  if Sys.file_exists project
  then
    Violet_surface.Reporter.fatalf
      Parse_error
      "cannot create project: %s already exists"
      project;
  let name = Filename.basename project in
  Unix.mkdir project 0o755;
  ignore (scaffold ~dir:project ~name);
  Printf.printf "created %s\n" project
;;

let cmd ~env =
  let _ = env in
  let arg_name =
    let doc = "Project directory to create (also used as the manifest \\name)." in
    Arg.required
    @@ Arg.pos 0 (Arg.some Arg.string) None
    @@ Arg.info [] ~docv:"PROJECT" ~doc
  in
  let doc = "Create a new violet project scaffold" in
  let info = Cmd.info "new" ~version ~doc in
  Cmd.v info Term.(const new_ $ arg_name)
;;
