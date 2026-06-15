open Cmdliner
open Cli_common

let load explicit_root filename =
  let deps = Hashtbl.create ~random:true 1000 in
  let mods = Hashtbl.create ~random:true 1000 in
  let m = Violet_surface.Parser.parse_file filename in
  let mode = Violet_project.Loader.mode_for_entry ?explicit_root filename in
  let entry_key = Violet_project.Loader.module_name m.name in
  Violet_project.Loader.prepare_dependencies mode [] mods deps entry_key m;
  elaborate mods deps;
  let entry = Hashtbl.find mods entry_key in
  Repl.run ~entry_module:entry
;;

let cmd ~env =
  let _ = env in
  let arg_file =
    let doc = "The program file to load." in
    Arg.required @@ Arg.pos 0 (Arg.some Arg.file) None @@ Arg.info [] ~docv:"PROG" ~doc
  in
  let doc = "Load input program file into REPL" in
  let man = [ `S Manpage.s_description; `P "" ] in
  let info = Cmd.info "load" ~version ~doc ~man in
  Cmd.v info Term.(const load $ arg_root $ arg_file)
;;
