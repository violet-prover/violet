open Cmdliner
open Cli_common
open Violet_common

let new_ ~stdout project =
  if Sys.file_exists project
  then Reporter.fatalf Parse_error "cannot create project: %s already exists" project;
  let name = Filename.basename project in
  Unix.mkdir project 0o755;
  ignore (scaffold ~stdout ~dir:project ~name);
  Eio.Flow.copy_string (Printf.sprintf "created %s\n" project) stdout
;;

let cmd ~env =
  let stdout = Eio.Stdenv.stdout env in
  let arg_name =
    let doc = "Project directory to create (also used as the manifest \\name)." in
    Arg.required
    @@ Arg.pos 0 (Arg.some Arg.string) None
    @@ Arg.info [] ~docv:"PROJECT" ~doc
  in
  let doc = "Create a new violet project scaffold" in
  let info = Cmd.info "new" ~version ~doc in
  Cmd.v info Term.(const (new_ ~stdout) $ arg_name)
;;
