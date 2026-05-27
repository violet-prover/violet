open Cmdliner
module Tty = Asai.Tty.Make (Violet_surface.Reporter.Message)

let version = "0.4.0"

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
        let m = Violet_surface.Parser.parse_file filename in
        let mode = Violet_project.Loader.mode_for_entry ?explicit_root filename in
        let entry_key = Violet_project.Loader.module_name m.name in
        Violet_project.Loader.prepare_dependencies mode [] mods deps entry_key m;
        (match Tsort.sort @@ List.of_seq @@ Hashtbl.to_seq deps with
         | Sorted r ->
           List.iter
             (fun mod_name ->
                let module_path = String.split_on_char '/' mod_name in
                Violet_elab.Elab.check_module ~module_path (Hashtbl.find mods mod_name))
             r
         | ErrorCycle err_list ->
           Violet_surface.Reporter.fatalf Parse_error "Cycle import %s"
           @@ String.concat ", " err_list);
        let entry = Hashtbl.find mods entry_key in
        Repl.run ~entry_module:entry)
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
          let m = Violet_surface.Parser.parse_file filename in
          let mode = Violet_project.Loader.mode_for_entry ?explicit_root filename in
          Violet_project.Loader.prepare_dependencies
            mode
            []
            mods
            deps
            (Violet_project.Loader.module_name m.name)
            m;
          (match Tsort.sort @@ List.of_seq @@ Hashtbl.to_seq deps with
           | Sorted r ->
             List.iter
               (fun mod_name ->
                  let module_path = String.split_on_char '/' mod_name in
                  Violet_elab.Elab.check_module ~module_path (Hashtbl.find mods mod_name))
               r
           | ErrorCycle err_list ->
             Violet_surface.Reporter.fatalf Parse_error "Cycle import %s"
             @@ String.concat ", " err_list)
        | None ->
          let root =
            match explicit_root with
            | Some r -> r
            | None ->
              (match Violet_project.Root.find_root (Sys.getcwd ()) with
               | Some r -> r
               | None ->
                 Violet_surface.Reporter.fatalf
                   Parse_error
                   "no info.vt found in cwd or its ancestors; pass a file or use --root")
          in
          let proj =
            try Violet_project.Resolve.load root with
            | Violet_project.Resolve.Project_error msg ->
              Violet_surface.Reporter.fatalf Parse_error "%s" msg
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
          (match Tsort.sort @@ List.of_seq @@ Hashtbl.to_seq deps with
           | Sorted r ->
             List.iter
               (fun mod_name ->
                  let module_path = String.split_on_char '/' mod_name in
                  Violet_elab.Elab.check_module ~module_path (Hashtbl.find mods mod_name))
               r
           | ErrorCycle err_list ->
             Violet_surface.Reporter.fatalf Parse_error "Cycle import %s"
             @@ String.concat ", " err_list))
      $ arg_root
      $ arg_file)
;;

let write_file path contents =
  let oc = open_out path in
  Fun.protect ~finally:(fun () -> close_out oc) @@ fun () -> output_string oc contents
;;

let new_cmd ~env =
  let _ = env in
  let arg_name =
    let doc = "Project directory to create (also used as the manifest \\name)." in
    Arg.required
    @@ Arg.pos 0 (Arg.some Arg.string) None
    @@ Arg.info [] ~docv:"PROJECT" ~doc
  in
  let doc = "Create a new violet project scaffold" in
  let info = Cmd.info "new" ~version ~doc in
  Cmd.v
    info
    Term.(
      const (fun project ->
        if Sys.file_exists project
        then
          Violet_surface.Reporter.fatalf
            Parse_error
            "cannot create project: %s already exists"
            project;
        let name = Filename.basename project in
        Unix.mkdir project 0o755;
        Unix.mkdir (Filename.concat project "src") 0o755;
        let info_path = Filename.concat project "info.vt" in
        write_file info_path (Printf.sprintf "\\name %S\n\\version \"0.1.0\"\n" name);
        Printf.printf "created %s\n" project)
      $ arg_name)
;;

let add_cmd ~env =
  let _ = env in
  let arg_root =
    let doc = "Explicit project root (directory containing info.vt)." in
    Arg.value @@ Arg.opt (Arg.some Arg.dir) None @@ Arg.info [ "root" ] ~docv:"DIR" ~doc
  in
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
  Cmd.v
    info
    Term.(
      const (fun explicit_root rev key url ->
        let root =
          match explicit_root with
          | Some r -> r
          | None ->
            (match Violet_project.Root.find_root (Sys.getcwd ()) with
             | Some r -> r
             | None ->
               Violet_surface.Reporter.fatalf
                 Parse_error
                 "no info.vt found in cwd or its ancestors")
        in
        let manifest =
          try Violet_project.Resolve.load_manifest root with
          | Violet_project.Resolve.Project_error msg ->
            Violet_surface.Reporter.fatalf Parse_error "%s" msg
        in
        if
          List.exists (fun (d : Violet_project.Manifest.dep) -> d.key = key) manifest.deps
        then Violet_surface.Reporter.fatalf Parse_error "dep `%s` is already declared" key;
        let info_path = Filename.concat root "info.vt" in
        let oc = open_out_gen [ Open_append; Open_creat ] 0o644 info_path in
        (Fun.protect ~finally:(fun () -> close_out oc)
         @@ fun () ->
         output_string oc (Printf.sprintf "\\dep %s (git = %S, rev = %S)\n" key url rev));
        Printf.printf "added dep `%s` -> %s@%s; run `violet update`\n" key url rev)
      $ arg_root
      $ arg_rev
      $ arg_key
      $ arg_url)
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
               Violet_surface.Reporter.fatalf
                 Parse_error
                 "no info.vt found in cwd or its ancestors")
        in
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
        Printf.printf "updated %s (%d git deps)\n" path (List.length entries))
      $ arg_root)
;;

let lsp_cmd ~env =
  let doc = "Start language server (LSP over stdio)" in
  let info = Cmd.info "lsp" ~version ~doc in
  let arg_stdio =
    Arg.value @@ Arg.flag @@ Arg.info [ "stdio" ] ~doc:"Use stdio transport (default)"
  in
  let run _stdio = Violet_langserver.Server.run ~env () in
  Cmd.v info Term.(const run $ arg_stdio)
;;

let cmd ~env =
  let doc = "violet" in
  let man = [ `S Manpage.s_bugs; `S Manpage.s_authors; `P "Lîm Tsú-thuàn" ] in
  let info = Cmd.info "violet" ~version ~doc ~man in
  Cmd.group
    info
    [ load_cmd ~env
    ; check_cmd ~env
    ; update_cmd ~env
    ; new_cmd ~env
    ; add_cmd ~env
    ; lsp_cmd ~env
    ]
;;

let () =
  let fatal diagnostics =
    Tty.display diagnostics;
    exit 1
  in
  Printexc.record_backtrace true;
  Eio_main.run
  @@ fun env ->
  Violet_surface.Reporter.run ~emit:Tty.display ~fatal
  @@ fun () ->
  let open Violet_elab.Context.Handler in
  Violet_elab.Context.S.run ~shadow ~not_found ~hook
  @@ fun () ->
  let open Violet_elab.Env.Handler in
  Violet_elab.Env.S.run ~shadow ~not_found ~hook
  @@ fun () -> exit @@ Cmd.eval ~catch:false @@ cmd ~env
;;
