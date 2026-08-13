open Cmdliner
open Cli_common
open Violet_common

let rec ensure_dir dir =
  if not (Sys.file_exists dir)
  then begin
    ensure_dir (Filename.dirname dir);
    Unix.mkdir dir 0o755
  end
;;

(* Write Violet's stylesheet to [path] (already fully resolved by
   [Weave]/[Delim] — project-root-relative attribute or absolute). Nothing is
   written unless a project's `\literate` rule asked for it via `css = ...`;
   there is no unconditional default location anymore (a rule targeting a
   non-HTML format has no use for a stylesheet at all). *)
let write_css ~stdout path =
  ensure_dir (Filename.dirname path);
  write_file path Violet_literate.Css.stylesheet;
  Eio.Flow.copy_string
    (Printf.sprintf "wrote %s (link it once from your site)\n" path)
    stdout
;;

let write_pages ~stdout dir pages =
  List.iter
    (fun (filename, content) ->
       let out_path = Filename.concat dir filename in
       ensure_dir (Filename.dirname out_path);
       write_file out_path content;
       Eio.Flow.copy_string (Printf.sprintf "wove %s\n" out_path) stdout)
    pages
;;

let weave ~stdout ~stderr explicit_root open_opt close_opt inline_css out out_dir file_opt
  =
  let explicit_delim =
    match open_opt, close_opt with
    | Some open_, Some close -> Some Violet_literate.Delim.{ open_; close }
    | None, None -> None
    | Some _, None | None, Some _ ->
      Reporter.fatalf Parse_error "weave: --open and --close must be given together"
  in
  if Option.is_some explicit_delim && Option.is_none file_opt
  then
    Reporter.fatalf
      Parse_error
      "weave: --open/--close only apply when weaving a single FILE (a whole-project \
       weave may span several extensions/rules at once)";
  if inline_css
  then
    Eio.Flow.copy_string
      "weave: --inline-css is not yet implemented; writing a stylesheet file instead, \
       per the matched rule's `css` attribute (if any)\n"
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
    (match
       Violet_literate.Weave.weave_file ?explicit_root ?explicit_delim ~scrbl_path ()
     with
     | None -> exit 1
     | Some (output, css_path) ->
       write_file out_path output;
       Option.iter (write_css ~stdout) css_path;
       Eio.Flow.copy_string (Printf.sprintf "wove %s -> %s\n" scrbl_path out_path) stdout)
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
    let pages, css_paths, failed = Violet_literate.Weave.weave_project ~root in
    write_pages ~stdout out_dir pages;
    List.iter (write_css ~stdout) css_paths;
    if failed > 0 then exit 1
;;

let cmd ~env =
  let stdout = Eio.Stdenv.stdout env in
  let stderr = Eio.Stdenv.stderr env in
  let arg_open =
    let doc =
      "Open token marking the start of a Violet block (paired with --close). Overrides \
       the project's literate rule for this one run; only valid when weaving a single \
       FILE. Both --open and --close must be given together."
    in
    Arg.value
    @@ Arg.opt (Arg.some Arg.string) None
    @@ Arg.info [ "open" ] ~docv:"STR" ~doc
  in
  let arg_close =
    let doc = "Close token marking the end of a Violet block (paired with --open)." in
    Arg.value
    @@ Arg.opt (Arg.some Arg.string) None
    @@ Arg.info [ "close" ] ~docv:"STR" ~doc
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
      "Output directory for a whole-project weave: each card writes <DIR>/<name>.<ext>. \
       Required when FILE is omitted."
    in
    Arg.value
    @@ Arg.opt (Arg.some Arg.string) None
    @@ Arg.info [ "out-dir" ] ~docv:"DIR" ~doc
  in
  let arg_file =
    let doc =
      "The literate document to weave. If omitted, weaves every card under \
       <project>/src/."
    in
    Arg.value @@ Arg.pos 0 (Arg.some Arg.file) None @@ Arg.info [] ~docv:"FILE" ~doc
  in
  let doc =
    "Weave a literate Violet document into its target format. Violet finds and \
     elaborates the code; how each rendered block embeds into the target format is \
     entirely determined by the project's `\\literate` rule for that file's extension in \
     info.vt (open/close escape tokens, an output command Violet pipes the rendered HTML \
     through, and an optional stylesheet destination) — there is no built-in backend."
  in
  let man = [ `S Manpage.s_description; `P "" ] in
  let info = Cmd.info "weave" ~version ~doc ~man in
  Cmd.v
    info
    Term.(
      const (weave ~stdout ~stderr)
      $ arg_root
      $ arg_open
      $ arg_close
      $ arg_inline_css
      $ arg_out
      $ arg_out_dir
      $ arg_file)
;;
