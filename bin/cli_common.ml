open Cmdliner
open Violet_common

let version = "0.8.0"

let write_file path contents =
  let oc = open_out path in
  Fun.protect ~finally:(fun () -> close_out oc) @@ fun () -> output_string oc contents
;;

(* The shared --root option, used by every project-aware subcommand. *)
let arg_root =
  let doc = "Explicit project root (directory containing info.vt)." in
  Arg.value @@ Arg.opt (Arg.some Arg.dir) None @@ Arg.info [ "root" ] ~docv:"DIR" ~doc
;;

(* Resolve the project root: an explicit --root, else search cwd's ancestors.
   [hint] is appended to the not-found message (e.g. "; pass a file or use --root"). *)
let require_root ?(hint = "") explicit_root =
  match explicit_root with
  | Some r -> r
  | None ->
    (match Violet_project.Root.find_root (Sys.getcwd ()) with
     | Some r -> r
     | None ->
       Reporter.fatalf Parse_error "no info.vt found in cwd or its ancestors%s" hint)
;;

(* Topologically sort the gathered dependencies and elaborate each module. *)
let elaborate mods deps =
  match Tsort.sort @@ List.of_seq @@ Hashtbl.to_seq deps with
  | Sorted r ->
    List.iter
      (fun mod_name ->
         let module_path = Violet_kernel.Syntax.Name.to_segments mod_name in
         Violet_elab.Elab.check_module ~module_path (Hashtbl.find mods mod_name))
      r
  | ErrorCycle err_list ->
    Reporter.fatalf Parse_error "Cycle import %s" @@ String.concat ", " err_list
;;

(* Create info.vt and src/ under [dir], each skipped if it already exists.
   Prints a skip/created line per item and returns what was created. *)
let scaffold ~dir ~name =
  let created = ref [] in
  let info_path = Filename.concat dir "info.vt" in
  if Sys.file_exists info_path
  then Printf.printf "skip info.vt (already exists)\n"
  else begin
    write_file info_path (Printf.sprintf "\\name %S\n\\version \"0.1.0\"\n" name);
    created := "info.vt" :: !created
  end;
  let src_path = Filename.concat dir "src" in
  if Sys.file_exists src_path
  then Printf.printf "skip src/ (already exists)\n"
  else begin
    Unix.mkdir src_path 0o755;
    created := "src/" :: !created
  end;
  List.rev !created
;;
