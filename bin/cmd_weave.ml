open Cmdliner
open Cli_common
open Violet_common

let write_stylesheet (dir : string) : string =
  let path = Filename.concat dir "violet.css" in
  write_file path Violet_literate.Css.stylesheet;
  path
;;

let weave explicit_root backend inline_css out out_dir file_opt =
  if not (String.equal backend "tr-notes")
  then
    Reporter.fatalf
      Parse_error
      "backend not yet implemented: %s (only `tr-notes`)"
      backend;
  if inline_css
  then prerr_endline "weave: --inline-css is not yet implemented; writing violet.css";
  match file_opt with
  | Some scrbl_path ->
    let out_path =
      match out with
      | Some p -> p
      | None ->
        Reporter.fatalf
          Parse_error
          "weave: -o/--output is required when weaving a single file"
    in
    (match Violet_literate.Weave.weave_file ?explicit_root ~scrbl_path () with
     | None -> exit 1
     | Some output ->
       write_file out_path output;
       let css = write_stylesheet (Filename.dirname out_path) in
       Printf.printf
         "wove %s -> %s (link %s once from your site)\n"
         scrbl_path
         out_path
         css)
  | None ->
    let out_dir =
      match out_dir with
      | Some d -> d
      | None ->
        Reporter.fatalf
          Parse_error
          "weave: --out-dir is required when weaving a whole project"
    in
    let root = require_root ~hint:"; pass a FILE or use --root" explicit_root in
    if not (Sys.file_exists out_dir) then Unix.mkdir out_dir 0o755;
    let registry = Violet_literate.TRCard.scan ~root in
    let cards = Violet_literate.TRCard.cards registry in
    let failed = ref 0 in
    List.iter
      (fun (addr, scrbl_path) ->
         match Violet_literate.Weave.weave_file ~explicit_root:root ~scrbl_path () with
         | None -> incr failed
         | Some output ->
           let out_path = Filename.concat out_dir (addr ^ ".scrbl") in
           write_file out_path output;
           Printf.printf "wove %s -> %s\n" scrbl_path out_path)
      cards;
    let css = write_stylesheet out_dir in
    Printf.printf "wrote %s (link it once from your site template)\n" css;
    if !failed > 0 then exit 1
;;

let cmd ~env =
  let _ = env in
  let arg_backend =
    let doc =
      "Output backend. Only `tr-notes` is implemented; a generic Scribble backend is \
       future work."
    in
    Arg.required
    @@ Arg.opt (Arg.some Arg.string) None
    @@ Arg.info [ "backend" ] ~docv:"BACKEND" ~doc
  in
  let arg_inline_css =
    let doc = "Reserved: inline the stylesheet (not yet implemented)." in
    Arg.value @@ Arg.flag @@ Arg.info [ "inline-css" ] ~doc
  in
  let arg_out =
    let doc = "Output file. Required when weaving a single FILE; there is no default." in
    Arg.value
    @@ Arg.opt (Arg.some Arg.string) None
    @@ Arg.info [ "o"; "output" ] ~docv:"OUT" ~doc
  in
  let arg_out_dir =
    let doc =
      "Output directory. Required in whole-project mode; each card writes \
       <DIR>/<addr>.scrbl."
    in
    Arg.value
    @@ Arg.opt (Arg.some Arg.string) None
    @@ Arg.info [ "out-dir" ] ~docv:"DIR" ~doc
  in
  let arg_file =
    let doc =
      "The .vt.scrbl card to weave. If omitted, weaves every card under <project>/src/."
    in
    Arg.value @@ Arg.pos 0 (Arg.some Arg.file) None @@ Arg.info [] ~docv:"FILE" ~doc
  in
  let doc = "Weave a literate Violet document (.vt.scrbl) into a .scrbl" in
  let man = [ `S Manpage.s_description; `P "" ] in
  let info = Cmd.info "weave" ~version ~doc ~man in
  Cmd.v
    info
    Term.(
      const weave
      $ arg_root
      $ arg_backend
      $ arg_inline_css
      $ arg_out
      $ arg_out_dir
      $ arg_file)
;;
