open Cmdliner
open Cli_common

let update explicit_root =
  let root = require_root explicit_root in
  let manifest =
    try Violet_project.Resolve.load_manifest root with
    | Violet_project.Resolve.Project_error msg ->
      Violet_surface.Reporter.fatalf Parse_error "%s" msg
  in
  let entries =
    List.filter_map
      (fun (d : Violet_project.Manifest.dep) ->
         match d.source with
         | Violet_project.Manifest.Path _ -> None
         | Violet_project.Manifest.Git { url; rev } ->
           let _, sha = Violet_project.Cache.ensure_clone ~url ~rev in
           Some Violet_project.Lockfile.{ key = d.key; url; rev = sha })
      manifest.deps
  in
  let lock = Violet_project.Lockfile.{ entries } in
  let path = Filename.concat root "info.lock" in
  let oc = open_out path in
  output_string oc (Violet_project.Lockfile.to_string lock);
  close_out oc;
  Printf.printf "updated %s (%d git deps)\n" path (List.length entries)
;;

let cmd ~env =
  let _ = env in
  let doc = "Resolve declared dependencies and regenerate info.lock" in
  let info = Cmd.info "update" ~version ~doc in
  Cmd.v info Term.(const update $ arg_root)
;;
