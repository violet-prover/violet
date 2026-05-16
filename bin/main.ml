open Cmdliner
module Tty = Asai.Tty.Make (Violet_elab.Reporter.Message)

let module_name filename = Filename.chop_extension @@ Filename.basename filename

type mode =
  | Project of Violet_project.Resolve.project
  | Single_file of string (* root directory used as fallback search base *)

let mode_for_entry ?explicit_root (filename : string) : mode =
  let mk_project root =
    try Project (Violet_project.Resolve.load root) with
    | Violet_project.Resolve.Project_error msg ->
      Violet_elab.Reporter.fatalf Parse_error "%s" msg
  in
  match explicit_root with
  | Some root -> mk_project root
  | None ->
    let start = Filename.dirname (Filename.concat (Sys.getcwd ()) filename) in
    (match Violet_project.Root.find_root start with
     | Some root -> mk_project root
     | None -> Single_file (Filename.dirname filename))
;;

let rec walk_vt_files (dir : string) : string list =
  if not (Sys.file_exists dir)
  then []
  else
    Sys.readdir dir
    |> Array.to_list
    |> List.concat_map (fun entry ->
      (* skip dotfiles and _build *)
      if String.length entry > 0 && entry.[0] = '.'
      then []
      else if entry = "_build"
      then []
      else (
        let full = Filename.concat dir entry in
        if Sys.is_directory full
        then walk_vt_files full
        else if Filename.check_suffix entry ".vt"
        then [ full ]
        else []))
;;

type dependencies = (string, string list) Hashtbl.t
type modules = (string, Violet_elab.Surface.t) Hashtbl.t

(* `prefix_segs` are the canonical module-path segments above the file being
   prepared. Each child's canonical key is `prefix_segs @ user_import`; the
   prefix grows by the crossed dep_key whenever an import crosses into a dep,
   so the same physical file gets a single canonical key regardless of which
   consumer's spelling reached it. The Surface.t stored in mods has its
   `imports` rewritten to canonical paths so the elaborator's `renaming` finds
   each imported module's section. *)
let rec prepare_dependencies
          (mode : mode)
          (prefix_segs : string list)
          (mods : modules)
          (deps : dependencies)
          (key : string)
          (m : Violet_elab.Surface.t)
  =
  if Hashtbl.mem deps key
  then ()
  else begin
    let canonical_libraries = List.map (fun lib -> prefix_segs @ lib) m.imports in
    Hashtbl.add mods key { m with imports = canonical_libraries };
    Hashtbl.add deps key (List.map (String.concat "/") canonical_libraries);
    List.iter2
      (fun user_library canonical_library ->
         let canonical_key = String.concat "/" canonical_library in
         let next_mode, next_segs, filepath =
           match mode with
           | Project proj ->
             let p, crossed, fp =
               Violet_project.Resolve.resolve_import_in proj user_library
             in
             let ns =
               match crossed with
               | Some k -> prefix_segs @ [ k ]
               | None -> prefix_segs
             in
             Project p, ns, fp
           | Single_file root ->
             ( mode
             , prefix_segs
             , Filename.concat root (String.concat "/" user_library ^ ".vt") )
         in
         let m = Violet_elab.Parser.parse_file filepath in
         prepare_dependencies next_mode next_segs mods deps canonical_key m)
      m.imports
      canonical_libraries
  end
;;

let version = "0.1.0"

let load_cmd ~env =
  let _ = env in
  let arg_file =
    let doc = "The program file to load." in
    Arg.required @@ Arg.pos 0 (Arg.some Arg.file) None @@ Arg.info [] ~docv:"PROG" ~doc
  in
  let arg_root =
    let doc = "Explicit project root (directory containing info.vt)." in
    Arg.value @@ Arg.opt (Arg.some Arg.dir) None @@ Arg.info [ "root" ] ~docv:"DIR" ~doc
  in
  let doc = "Load input program file into REPL" in
  let man = [ `S Manpage.s_description; `P "" ] in
  let info = Cmd.info "load" ~version ~doc ~man in
  Cmd.v
    info
    Term.(
      const (fun explicit_root filename ->
        let deps = Hashtbl.create ~random:true 1000 in
        let mods = Hashtbl.create ~random:true 1000 in
        let m = Violet_elab.Parser.parse_file filename in
        let mode = mode_for_entry ?explicit_root filename in
        prepare_dependencies mode [] mods deps (module_name m.name) m;
        (match Tsort.sort @@ List.of_seq @@ Hashtbl.to_seq deps with
         | Sorted r ->
           List.iter
             (fun mod_name ->
                let module_path = String.split_on_char '/' mod_name in
                Violet_elab.Elab.check_module ~module_path (Hashtbl.find mods mod_name))
             r
         | ErrorCycle err_list ->
           Violet_elab.Reporter.fatalf Parse_error "Cycle import %s"
           @@ String.concat ", " err_list);
        (* TODO: load module into a REPL *)
        ())
      $ arg_root
      $ arg_file)
;;

let check_cmd ~env =
  let _ = env in
  let arg_root =
    let doc = "Explicit project root (directory containing info.vt)." in
    Arg.value @@ Arg.opt (Arg.some Arg.dir) None @@ Arg.info [ "root" ] ~docv:"DIR" ~doc
  in
  let arg_file =
    let doc =
      "The program file to check. If omitted, checks every .vt under <project>/src/."
    in
    Arg.value @@ Arg.pos 0 (Arg.some Arg.file) None @@ Arg.info [] ~docv:"PROG" ~doc
  in
  let doc = "Check input program file (or the whole project)" in
  let man = [ `S Manpage.s_description; `P "" ] in
  let info = Cmd.info "check" ~version ~doc ~man in
  Cmd.v
    info
    Term.(
      const (fun explicit_root file_opt ->
        let deps = Hashtbl.create ~random:true 1000 in
        let mods = Hashtbl.create ~random:true 1000 in
        match file_opt with
        | Some filename ->
          let m = Violet_elab.Parser.parse_file filename in
          let mode = mode_for_entry ?explicit_root filename in
          prepare_dependencies mode [] mods deps (module_name m.name) m;
          (match Tsort.sort @@ List.of_seq @@ Hashtbl.to_seq deps with
           | Sorted r ->
             List.iter
               (fun mod_name ->
                  let module_path = String.split_on_char '/' mod_name in
                  Violet_elab.Elab.check_module ~module_path (Hashtbl.find mods mod_name))
               r
           | ErrorCycle err_list ->
             Violet_elab.Reporter.fatalf Parse_error "Cycle import %s"
             @@ String.concat ", " err_list)
        | None ->
          let root =
            match explicit_root with
            | Some r -> r
            | None ->
              (match Violet_project.Root.find_root (Sys.getcwd ()) with
               | Some r -> r
               | None ->
                 Violet_elab.Reporter.fatalf
                   Parse_error
                   "no info.vt found in cwd or its ancestors; pass a file or use --root")
          in
          let proj =
            try Violet_project.Resolve.load root with
            | Violet_project.Resolve.Project_error msg ->
              Violet_elab.Reporter.fatalf Parse_error "%s" msg
          in
          let mode = Project proj in
          let src_dir = Filename.concat root "src" in
          let files = walk_vt_files src_dir in
          List.iter
            (fun filename ->
               let m = Violet_elab.Parser.parse_file filename in
               prepare_dependencies mode [] mods deps (module_name m.name) m)
            files;
          (match Tsort.sort @@ List.of_seq @@ Hashtbl.to_seq deps with
           | Sorted r ->
             List.iter
               (fun mod_name ->
                  let module_path = String.split_on_char '/' mod_name in
                  Violet_elab.Elab.check_module ~module_path (Hashtbl.find mods mod_name))
               r
           | ErrorCycle err_list ->
             Violet_elab.Reporter.fatalf Parse_error "Cycle import %s"
             @@ String.concat ", " err_list))
      $ arg_root
      $ arg_file)
;;

let update_cmd ~env =
  let _ = env in
  let arg_root =
    let doc = "Explicit project root (directory containing info.vt)." in
    Arg.value @@ Arg.opt (Arg.some Arg.dir) None @@ Arg.info [ "root" ] ~docv:"DIR" ~doc
  in
  let doc = "Resolve declared dependencies and regenerate info.lock" in
  let info = Cmd.info "update" ~version ~doc in
  Cmd.v
    info
    Term.(
      const (fun explicit_root ->
        let root =
          match explicit_root with
          | Some r -> r
          | None ->
            (match Violet_project.Root.find_root (Sys.getcwd ()) with
             | Some r -> r
             | None ->
               Violet_elab.Reporter.fatalf
                 Parse_error
                 "no info.vt found in cwd or its ancestors")
        in
        let manifest =
          try Violet_project.Resolve.load_manifest root with
          | Violet_project.Resolve.Project_error msg ->
            Violet_elab.Reporter.fatalf Parse_error "%s" msg
        in
        let entries =
          List.filter_map
            (fun (d : Violet_project.Manifest.dep) ->
               match d.source with
               | Violet_project.Manifest.Path _ -> None
               | Violet_project.Manifest.Git { url; rev } ->
                 let _ : string = Violet_project.Cache.ensure_clone ~url ~rev in
                 Some Violet_project.Lockfile.{ key = d.key; url; rev })
            manifest.deps
        in
        let lock = Violet_project.Lockfile.{ entries } in
        let path = Filename.concat root "info.lock" in
        let oc = open_out path in
        output_string oc (Violet_project.Lockfile.to_string lock);
        close_out oc;
        Printf.printf "updated %s (%d git deps)\n" path (List.length entries))
      $ arg_root)
;;

let cmd ~env =
  let doc = "violet" in
  let man = [ `S Manpage.s_bugs; `S Manpage.s_authors; `P "Lîm Tsú-thuàn" ] in
  let info = Cmd.info "violet" ~version ~doc ~man in
  Cmd.group info [ load_cmd ~env; check_cmd ~env; update_cmd ~env ]
;;

let () =
  let fatal diagnostics =
    Tty.display diagnostics;
    exit 1
  in
  Printexc.record_backtrace true;
  Eio_main.run
  @@ fun env ->
  Violet_elab.Reporter.run ~emit:Tty.display ~fatal
  @@ fun () ->
  let open Violet_elab.Context.Handler in
  Violet_elab.Context.S.run ~shadow ~not_found ~hook
  @@ fun () ->
  let open Violet_elab.Env.Handler in
  Violet_elab.Env.S.run ~shadow ~not_found ~hook
  @@ fun () -> exit @@ Cmd.eval ~catch:false @@ cmd ~env
;;
