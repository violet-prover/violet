open Cmdliner
open Cli_common

let add explicit_root rev key url =
  let root = require_root explicit_root in
  let manifest =
    try Violet_project.Resolve.load_manifest root with
    | Violet_project.Resolve.Project_error msg ->
      Violet_surface.Reporter.fatalf Parse_error "%s" msg
  in
  if List.exists (fun (d : Violet_project.Manifest.dep) -> d.key = key) manifest.deps
  then Violet_surface.Reporter.fatalf Parse_error "dep `%s` is already declared" key;
  let info_path = Filename.concat root "info.vt" in
  let oc = open_out_gen [ Open_append; Open_creat ] 0o644 info_path in
  (Fun.protect ~finally:(fun () -> close_out oc)
   @@ fun () ->
   output_string oc (Printf.sprintf "\\dep %s (git = %S, rev = %S)\n" key url rev));
  Printf.printf "added dep `%s` -> %s@%s; run `violet update`\n" key url rev
;;

let cmd ~env =
  let _ = env in
  let arg_rev =
    let doc = "Git revision to pin in info.vt (branch, tag, or commit)." in
    Arg.value @@ Arg.opt Arg.string "main" @@ Arg.info [ "rev" ] ~docv:"REV" ~doc
  in
  let arg_key =
    let doc = "Dependency key (the prefix used in import paths)." in
    Arg.required @@ Arg.pos 0 (Arg.some Arg.string) None @@ Arg.info [] ~docv:"KEY" ~doc
  in
  let arg_url =
    let doc = "Git URL of the dependency." in
    Arg.required @@ Arg.pos 1 (Arg.some Arg.string) None @@ Arg.info [] ~docv:"URL" ~doc
  in
  let doc = "Add a git dependency to info.vt" in
  let info = Cmd.info "add" ~version ~doc in
  Cmd.v info Term.(const add $ arg_root $ arg_rev $ arg_key $ arg_url)
;;
