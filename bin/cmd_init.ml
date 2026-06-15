open Cmdliner
open Cli_common

let init dir =
  if not (Sys.file_exists dir && Sys.is_directory dir)
  then
    Violet_surface.Reporter.fatalf
      Parse_error
      "cannot initialize: %s is not an existing directory"
      dir;
  let name = Filename.basename (if dir = "." then Sys.getcwd () else dir) in
  match scaffold ~dir ~name with
  | [] -> Printf.printf "nothing to do; project already initialized\n"
  | xs -> Printf.printf "created %s\n" (String.concat ", " xs)
;;

let cmd ~env =
  let _ = env in
  let arg_dir =
    let doc = "Directory to initialize. Defaults to the current directory." in
    Arg.value @@ Arg.pos 0 Arg.string "." @@ Arg.info [] ~docv:"DIR" ~doc
  in
  let doc = "Initialize info.vt and src/ in an existing directory" in
  let info = Cmd.info "init" ~version ~doc in
  Cmd.v info Term.(const init $ arg_dir)
;;
