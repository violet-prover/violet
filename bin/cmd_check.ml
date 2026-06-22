open Cmdliner
open Cli_common
open Violet_common

let check explicit_root file_opt =
  let deps = Hashtbl.create ~random:true 1000 in
  let mods = Hashtbl.create ~random:true 1000 in
  match file_opt with
  | Some filename when Filename.check_suffix filename ".scrbl" ->
    (* A literate [.vt.scrbl] card is a scribble document, not raw Violet source:
       parsing it directly chokes on the prose (e.g. [@date{...}]). Route it
       through the weaver's elaboration, which scans the [@vt|{}|] blocks, checks
       the synthesized module, and re-anchors diagnostics onto the scrbl. *)
    (match Violet_literate.Weave.elaborate ?explicit_root ~scrbl_path:filename () with
     | Some _ -> ()
     | None -> exit 1)
  | Some filename ->
    let m = Violet_surface.Parser.parse_file filename in
    let mode = Violet_project.Loader.mode_for_entry ?explicit_root filename in
    Violet_project.Loader.prepare_dependencies
      mode
      []
      mods
      deps
      (Violet_project.Loader.module_name m.name)
      m;
    elaborate mods deps
  | None ->
    let root = require_root ~hint:"; pass a file or use --root" explicit_root in
    let proj =
      try Violet_project.Resolve.load root with
      | Violet_project.Resolve.Project_error msg -> Reporter.fatalf Parse_error "%s" msg
    in
    let mode = Violet_project.Loader.Project proj in
    let src_dir = Filename.concat root "src" in
    let files = Violet_project.Loader.walk_vt_files src_dir in
    List.iter
      (fun filename ->
         let m = Violet_surface.Parser.parse_file filename in
         Violet_project.Loader.prepare_dependencies
           mode
           []
           mods
           deps
           (Violet_project.Loader.module_name m.name)
           m)
      files;
    elaborate mods deps
;;

let cmd ~env =
  let _ = env in
  let arg_file =
    let doc =
      "The program file to check. If omitted, checks every .vt under <project>/src/."
    in
    Arg.value @@ Arg.pos 0 (Arg.some Arg.file) None @@ Arg.info [] ~docv:"PROG" ~doc
  in
  let doc = "Check input program file (or the whole project)" in
  let man = [ `S Manpage.s_description; `P "" ] in
  let info = Cmd.info "check" ~version ~doc ~man in
  Cmd.v info Term.(const check $ arg_root $ arg_file)
;;
