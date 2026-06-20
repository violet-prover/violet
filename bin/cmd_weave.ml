open Cmdliner
open Cli_common
open Violet_common

let write_stylesheet (dir : string) : string =
  let path = Filename.concat dir "violet.css" in
  write_file path Violet_literate.Css.stylesheet;
  path
;;

(* Create [dir] and every missing ancestor (a dep page's path like
   [std/id/index.html] carries directories). *)
let rec ensure_dir dir =
  if not (Sys.file_exists dir)
  then begin
    ensure_dir (Filename.dirname dir);
    Unix.mkdir dir 0o755
  end
;;

(* Write each [(addr, html)] page under [dir] at [Weave.output_path], emitting a
   message per file. *)
let write_pages ~stdout dir pages =
  List.iter
    (fun (addr, html) ->
       let out_path = Filename.concat dir (Violet_literate.Weave.output_path ~addr) in
       ensure_dir (Filename.dirname out_path);
       write_file out_path html;
       Eio.Flow.copy_string (Printf.sprintf "wove %s\n" out_path) stdout)
    pages
;;

let weave ~stdout ~stderr explicit_root backend inline_css out out_dir file_opt =
  if not (String.equal backend "tr-notes")
  then
    Reporter.fatalf
      Parse_error
      "backend not yet implemented: %s (only `tr-notes`)"
      backend;
  if inline_css
  then
    Eio.Flow.copy_string
      "weave: --inline-css is not yet implemented; writing violet.css\n"
      stderr;
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
     | Some (output, dep_pages) ->
       write_file out_path output;
       let css = write_stylesheet (Filename.dirname out_path) in
       (* The card's referenced dependency pages are self-contained HTML; emit
          them under [--out-dir] (e.g. the site's _build) when given, so the
          cross-package /<dep>/<addr> links resolve. Without it they are skipped
          (the card still weaves, the links just 404). *)
       (match out_dir with
        | Some dir when dep_pages <> [] ->
          ensure_dir dir;
          write_pages ~stdout dir dep_pages;
          ignore (write_stylesheet dir)
        | _ -> ());
       Eio.Flow.copy_string
         (Printf.sprintf
            "wove %s -> %s (link %s once from your site)\n"
            scrbl_path
            out_path
            css)
         stdout)
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
    ensure_dir out_dir;
    let pages, failed = Violet_literate.Weave.weave_project ~root in
    write_pages ~stdout out_dir pages;
    let css = write_stylesheet out_dir in
    Eio.Flow.copy_string
      (Printf.sprintf "wrote %s (link it once from your site template)\n" css)
      stdout;
    if failed > 0 then exit 1
;;

let cmd ~env =
  let stdout = Eio.Stdenv.stdout env in
  let stderr = Eio.Stdenv.stderr env in
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
      "Output directory for self-contained dependency pages: each referenced dependency \
       module writes <DIR>/<dep>/<addr>/index.html (so the /<dep>/<addr> URL resolves by \
       directory index) plus a violet.css. With a single FILE this is optional (omit it \
       to skip dep pages); in whole-project mode it is required and also receives each \
       card's <addr>.scrbl."
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
      const (weave ~stdout ~stderr)
      $ arg_root
      $ arg_backend
      $ arg_inline_css
      $ arg_out
      $ arg_out_dir
      $ arg_file)
;;
