open Cmdliner
open Cli_common
open Violet_common

let init ~stdout dir =
  if not (Sys.file_exists dir && Sys.is_directory dir)
  then
    Reporter.fatalf Parse_error "cannot initialize: %s is not an existing directory" dir;
  let name = Filename.basename (if dir = "." then Sys.getcwd () else dir) in
  match scaffold ~stdout ~dir ~name with
  | [] -> Eio.Flow.copy_string "nothing to do; project already initialized\n" stdout
  | xs ->
    Eio.Flow.copy_string (Printf.sprintf "created %s\n" (String.concat ", " xs)) stdout
;;

let cmd ~env =
  let stdout = Eio.Stdenv.stdout env in
  let arg_dir =
    let doc = "Directory to initialize. Defaults to the current directory." in
    Arg.value @@ Arg.pos 0 Arg.string "." @@ Arg.info [] ~docv:"DIR" ~doc
  in
  let doc = "Initialize info.vt and src/ in an existing directory" in
  let info = Cmd.info "init" ~version ~doc in
  Cmd.v info Term.(const (init ~stdout) $ arg_dir)
;;
