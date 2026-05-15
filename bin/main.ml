open Cmdliner
module Tty = Asai.Tty.Make (Violet_elab.Reporter.Message)

let module_name filename = Filename.chop_extension @@ Filename.basename filename

type dependencies = (string, string list) Hashtbl.t
type modules = (string, Violet_elab.Surface.t) Hashtbl.t

let rec prepare_dependencies
          (root : string)
          (mods : modules)
          (deps : dependencies)
          (m : Violet_elab.Surface.t)
  =
  let key = module_name m.name in
  Hashtbl.add mods key m;
  let values = List.map (fun path -> String.concat "/" path) m.imports in
  match Hashtbl.find_opt deps key with
  | Some _ -> ()
  | None ->
    Hashtbl.add deps key values;
    List.iter
      (fun library ->
         let filepath = root ^ "/" ^ String.concat "/" library ^ ".vt" in
         let m = Violet_elab.Parser.parse_file filepath in
         prepare_dependencies root mods deps m)
      m.imports
;;

let version = "0.1.0"

let load_cmd ~env =
  let _ = env in
  let arg_file =
    let doc = "The program file to load." in
    Arg.required @@ Arg.pos 0 (Arg.some Arg.file) None @@ Arg.info [] ~docv:"PROG" ~doc
  in
  let doc = "Load input program file into REPL" in
  let man = [ `S Manpage.s_description; `P "" ] in
  let info = Cmd.info "load" ~version ~doc ~man in
  Cmd.v
    info
    Term.(
      const (fun filename ->
        let deps = Hashtbl.create ~random:true 1000 in
        let mods = Hashtbl.create ~random:true 1000 in
        let m = Violet_elab.Parser.parse_file filename in
        prepare_dependencies (Filename.dirname m.name) mods deps m;
        (match Tsort.sort @@ List.of_seq @@ Hashtbl.to_seq deps with
         | Sorted r ->
           List.iter
             (fun mod_name -> Violet_elab.Elab.check_module (Hashtbl.find mods mod_name))
             r
         | ErrorCycle err_list ->
           Violet_elab.Reporter.fatalf Parse_error "Cycle import %s"
           @@ String.concat ", " err_list);
        (* TODO: load module into a REPL *)
        ())
      $ arg_file)
;;

let check_cmd ~env =
  let _ = env in
  let arg_file =
    let doc = "The program file to check." in
    Arg.required @@ Arg.pos 0 (Arg.some Arg.file) None @@ Arg.info [] ~docv:"PROG" ~doc
  in
  let doc = "Check input program file" in
  let man = [ `S Manpage.s_description; `P "" ] in
  let info = Cmd.info "check" ~version ~doc ~man in
  Cmd.v
    info
    Term.(
      const (fun filename ->
        let deps = Hashtbl.create ~random:true 1000 in
        let mods = Hashtbl.create ~random:true 1000 in
        let m = Violet_elab.Parser.parse_file filename in
        prepare_dependencies (Filename.dirname m.name) mods deps m;
        match Tsort.sort @@ List.of_seq @@ Hashtbl.to_seq deps with
        | Sorted r ->
          List.iter
            (fun mod_name -> Violet_elab.Elab.check_module (Hashtbl.find mods mod_name))
            r
        | ErrorCycle err_list ->
          Violet_elab.Reporter.fatalf Parse_error "Cycle import %s"
          @@ String.concat ", " err_list)
      $ arg_file)
;;

let cmd ~env =
  let doc = "violet" in
  let man = [ `S Manpage.s_bugs; `S Manpage.s_authors; `P "Lîm Tsú-thuàn" ] in
  let info = Cmd.info "violet" ~version ~doc ~man in
  Cmd.group info [ load_cmd ~env; check_cmd ~env ]
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
