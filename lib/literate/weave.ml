(* Orchestrate a literate weave: scan a card written in any host document
   format configured via [\literate] in info.vt, elaborate its code, render
   each block to a semantically-annotated HTML fragment, and pipe that
   fragment through the project's per-extension output hook to reassemble the
   final document. Violet owns finding blocks (the escape delimiter) and
   understanding the code (elaboration, hover, jump metadata); embedding the
   rendered result into a target format is entirely the hook's job — see
   ../../docs/superpowers/specs/2026-08-13-weave-output-hook-design.md. *)

module Loader = Violet_project.Loader
module Index = Violet_interactive.Index
module Tty = Asai.Tty.Make (Violet_common.Reporter.Message)
open Source

(* The project's [\literate] rules governing the file at [path]: reuses an
   already-loaded project's manifest when [path] is being elaborated as part
   of one ([Loader.Project]); otherwise searches [path]'s own ancestors for a
   project (a dependency file may belong to a different project than the
   card being woven). No project found => no rules => [Delim.rule_for] will
   raise a clear "no \literate rule configured" error for that extension. *)
let literate_rules_near (path : string) : Violet_project.Manifest.literate_rule list =
  match Violet_project.Root.find_root (Filename.dirname path) with
  | Some root ->
    (try (Violet_project.Resolve.load_manifest root).literate with
     | Violet_project.Resolve.Project_error _ -> [])
  | None -> []
;;

let literate_rules_for (mode : Loader.mode) (path : string)
  : Violet_project.Manifest.literate_rule list
  =
  match mode with
  | Loader.Project proj -> proj.Violet_project.Resolve.manifest.literate
  | Loader.Single_file _ -> literate_rules_near path
;;

(* When the loader resolves an import to a plain [.vt] path, check whether a
   literate sibling exists for any of that file's project's configured
   extensions (e.g. [foo.vt] -> [foo.vt.md] or [foo.vt.scrbl]) and, if so,
   feed the concatenated block source instead of trying to parse the [.vt]
   stub as ordinary Violet syntax. *)
let text_override (filepath : string) : string option =
  if Filename.check_suffix filepath ".vt"
  then (
    let rules = literate_rules_near filepath in
    List.find_map
      (fun (r : Violet_project.Manifest.literate_rule) ->
         let card_path = filepath ^ r.ext in
         if Sys.file_exists card_path
         then (
           let delim = Delim.{ open_ = r.open_; close = r.close } in
           let _, blocks =
             build_buffer (Block.scan ~delim ~source:card_path (read_file card_path))
           in
           let b = Buffer.create 256 in
           List.iter
             (fun wb ->
                Buffer.add_string b wb.src;
                Buffer.add_char b '\n')
             blocks;
           Some (Buffer.contents b))
         else None)
      rules)
  else None
;;

(* Everything one card's source yields once elaborated: the semantic index
   plus the document structure needed to splice rendered HTML back in.
   [output_cmd]/[css_path] are resolved once per card (one file = one
   extension = one rule) — [output_cmd] is reused for every block in it;
   [css_path] (an absolute path, project-root-relative resolution already
   applied) is [None] unless the matched rule asked for a stylesheet. *)
type card_elab =
  { entries : Index.entry list
  ; def_paths : (string list, unit) Hashtbl.t
  ; segments : Block.segment list
  ; blocks : woven_block list
  ; module_file : string (* [buffer_source] for the card's own blocks *)
  ; output_cmd : string
  ; css_path : string option
  ; scrbl_path : string
  }

(* [proj_root]/[css] -> the absolute path to write the stylesheet to, if any:
   a relative [css] resolves against the project root (matching how `\dep
   (path = ...)` resolves), an absolute one is used as-is. *)
let resolve_css_path ~(proj_root : string) (css : string option) : string option =
  Option.map
    (fun c -> if Filename.is_relative c then Filename.concat proj_root c else c)
    css
;;

(* Elaborate one card. Returns [Some elab] on success, or [None] after
   printing elaboration diagnostics (remapped to the source document where
   possible). *)
let elaborate ?explicit_root ?explicit_delim ~(scrbl_path : string) () : card_elab option =
  let scrbl_text = read_file scrbl_path in
  let module_file =
    if Filename.check_suffix scrbl_path ".scrbl"
    then Filename.chop_extension scrbl_path
    else scrbl_path
  in
  let mode = Loader.mode_for_entry ?explicit_root module_file in
  let rules = literate_rules_for mode scrbl_path in
  let proj_root =
    match mode with
    | Loader.Project proj -> proj.Violet_project.Resolve.root
    | Loader.Single_file dir -> dir
  in
  let diag_collector = Violet_common.Diagnostic_collector.create () in
  let collector = Violet_interactive.Collector.create () in
  let on_event = Violet_interactive.Collector.on_event collector in
  let aborted = ref false in
  (* Delimiter resolution and scanning happen inside [Reporter.run] below so a
     missing \literate rule or an unterminated block reports through the same
     diagnostic path as elaboration errors, rather than escaping as an
     unhandled effect. *)
  let segments = ref []
  and blocks = ref []
  and output_cmd = ref ""
  and css_path = ref None in
  (try
     Violet_common.Reporter.run
       ~emit:(fun d -> Violet_common.Diagnostic_collector.emit diag_collector d)
       ~fatal:(fun d ->
         Violet_common.Diagnostic_collector.emit diag_collector d;
         aborted := true;
         raise Exit)
       (fun () ->
          let open Violet_elab in
          Context.S.run
            ~shadow:Context.Handler.shadow
            ~not_found:Context.Handler.not_found
            ~hook:Context.Handler.hook
          @@ fun () ->
          Env.S.run
            ~shadow:Env.Handler.shadow
            ~not_found:Env.Handler.not_found
            ~hook:Env.Handler.hook
          @@ fun () ->
          let delim, rule =
            Delim.resolve ?explicit:explicit_delim ~path:scrbl_path rules
          in
          output_cmd := rule.output;
          css_path := resolve_css_path ~proj_root rule.css;
          let segs, buffer, blks = to_buffer ~delim ~source:scrbl_path scrbl_text in
          segments := segs;
          blocks := blks;
          let m = Violet_surface.Parser.parse_buffer ~filename:module_file buffer in
          let deps = Hashtbl.create 16 in
          let mods = Hashtbl.create 16 in
          Loader.prepare_dependencies
            ~text_override
            mode
            []
            mods
            deps
            (Loader.module_name m.name)
            m;
          match Tsort.sort @@ List.of_seq @@ Hashtbl.to_seq deps with
          | Sorted r ->
            List.iter
              (fun mn ->
                 let mp = Violet_kernel.Syntax.Name.to_segments mn in
                 Elab.check_module ~on_event ~module_path:mp (Hashtbl.find mods mn))
              r
          | ErrorCycle _ -> ())
   with
   | Exit -> ());
  let errors = Violet_common.Diagnostic_collector.errors diag_collector in
  if !aborted || errors <> []
  then begin
    (* Re-anchor each diagnostic onto the source document so [Tty.display]
       highlights the real source, like [violet check]. Elaboration errors
       point into the synthesized buffer; scan/resolve errors already point
       into the document. A loc that maps nowhere is dropped (the message
       still renders, snippetless). *)
    List.iter
      (fun (d : Violet_common.Reporter.Message.t Asai.Diagnostic.t) ->
         let loc =
           Option.bind
             d.explanation.loc
             (remap_range ~blocks:!blocks ~scrbl_path ~scrbl_text ~module_file)
         in
         Tty.display { d with explanation = { d.explanation with loc } })
      errors;
    None
  end
  else begin
    let index = Violet_interactive.Collector.to_index collector in
    let entries = Index.all_entries index in
    let def_paths : (string list, unit) Hashtbl.t = Hashtbl.create 64 in
    List.iter
      (fun (e : Index.entry) ->
         if e.kind = Index.Def then Hashtbl.replace def_paths e.path ())
      entries;
    Some
      { entries
      ; def_paths
      ; segments = !segments
      ; blocks = !blocks
      ; module_file
      ; output_cmd = !output_cmd
      ; css_path = !css_path
      ; scrbl_path
      }
  end
;;

(* Render one card: verbatim segments pass through untouched; each code
   block's highlighted HTML fragment is piped through the card's resolved
   output hook and the result spliced back in. *)
let render_card (e : card_elab) : string =
  let out = Buffer.create 1024 in
  let blk_q = ref e.blocks in
  List.iter
    (fun seg ->
       match seg with
       | Block.Verbatim s -> Buffer.add_string out s
       | Block.Block _ ->
         let wb = List.hd !blk_q in
         blk_q := List.tl !blk_q;
         let html =
           Highlight.render
             ~src:wb.src
             ~buf_offset:wb.buf_start
             ~buffer_source:e.module_file
             ~entries:e.entries
             ~def_paths:e.def_paths
         in
         Buffer.add_string out (Output_hook.run ~cmd:e.output_cmd html))
    e.segments;
  Buffer.contents out
;;

(* Weave one card. Returns [Some (rendered, css_path)] on success — [css_path]
   is where to write Violet's stylesheet, if the matched rule asked for one —
   or [None] after printing elaboration diagnostics. *)
let weave_file ?explicit_root ?explicit_delim ~(scrbl_path : string) ()
  : (string * string option) option
  =
  Option.map
    (fun e -> render_card e, e.css_path)
    (elaborate ?explicit_root ?explicit_delim ~scrbl_path ())
;;

(* Basename with [ext] and a trailing [.vt] stripped, e.g. "foo.vt.md" with
   [ext = ".md"] -> ["foo"]. [None] if [entry] doesn't have that shape (not
   every file with a configured extension is a literate card — only ones
   following the [<name>.vt.<ext>] convention). *)
let card_name (ext : string) (entry : string) : string option =
  if Filename.check_suffix entry ext
  then (
    let stem = String.sub entry 0 (String.length entry - String.length ext) in
    if Filename.check_suffix stem ".vt" then Some (Filename.chop_extension stem) else None)
  else None
;;

(* Scan [dir] for every file matching one of [rules]' extensions and the
   [<name>.vt.<ext>] naming convention, as [(name, ext, path)] triples. Reuses
   [Loader.walk_files]'s traversal (skip dotfiles/[_build]/[_tmp], recurse
   into directories) — only the per-entry match against the project's
   dynamically-configured rules is specific to card discovery. *)
let walk_cards (rules : Violet_project.Manifest.literate_rule list) (dir : string)
  : (string * string * string) list
  =
  let rule_match entry =
    List.find_map
      (fun (r : Violet_project.Manifest.literate_rule) ->
         Option.map (fun name -> name, r.ext) (card_name r.ext entry))
      rules
  in
  Loader.walk_files ~keep:(fun entry -> Option.is_some (rule_match entry)) dir
  |> List.filter_map (fun full ->
    Option.map (fun (name, ext) -> name, ext, full) (rule_match (Filename.basename full)))
;;

(* Weave every card under [<root>/src]. Returns [(filename, output)] pairs —
   [filename] is the card's name with its own extension, e.g. ["foo.md"] —
   the distinct stylesheet paths any woven card's rule asked for (a project
   mixing formats may only need one, or none), and the count of cards that
   failed to elaborate. *)
let weave_project ~(root : string) : (string * string) list * string list * int =
  let rules =
    try (Violet_project.Resolve.load_manifest root).literate with
    | Violet_project.Resolve.Project_error _ -> []
  in
  let cards = walk_cards rules (Filename.concat root "src") in
  let failed = ref 0 in
  let css_paths = Hashtbl.create 4 in
  let pages =
    List.filter_map
      (fun (name, ext, path) ->
         match elaborate ~explicit_root:root ~scrbl_path:path () with
         | Some e ->
           Option.iter (fun p -> Hashtbl.replace css_paths p ()) e.css_path;
           Some (name ^ ext, render_card e)
         | None ->
           incr failed;
           None)
      cards
  in
  pages, Hashtbl.fold (fun p () acc -> p :: acc) css_paths [], !failed
;;

let contains (s : string) (sub : string) : bool =
  let n = String.length s
  and m = String.length sub in
  let rec go i = i + m <= n && (String.equal (String.sub s i m) sub || go (i + 1)) in
  go 0
;;

let write_test_file dir rel content =
  let path = Filename.concat dir rel in
  let d = Filename.dirname path in
  if not (Sys.file_exists d) then Unix.mkdir d 0o755;
  let oc = open_out path in
  output_string oc content;
  close_out oc
;;

let default_literate_manifest =
  {| \literate ".scrbl" (open = "@vt|{", close = "}|", output = "cat") |}
;;

let%test "weave resolves definitions and emits data-vt metadata for uses" =
  let root = Filename.temp_dir "litweave" "" in
  Unix.mkdir (Filename.concat root "src") 0o755;
  write_test_file
    root
    "info.vt"
    (Printf.sprintf "\\name \"lit\"\n\\version \"0.1.0\"\n%s\n" default_literate_manifest);
  write_test_file
    root
    "src/a.vt.scrbl"
    "@p{a}\n\
     @vt|{\n\
     \\universe U\n\
     \\export id\n\
     \\let id (A : U) : A -> A \\where\n\
    \  <= \\intro\n\
    \  | id A x => x\n\
     }|\n";
  match
    weave_file ~explicit_root:root ~scrbl_path:(Filename.concat root "src/a.vt.scrbl") ()
  with
  | None -> false
  | Some (s, css) ->
    contains s "data-vt-kind=\"def\""
    && contains s "id=\"vt-def-id\""
    && contains s "@p{a}"
    && css = None
;;

let%test "weave carries cross-file resolution as data-vt-target-* attributes" =
  let root = Filename.temp_dir "litweave" "" in
  Unix.mkdir (Filename.concat root "src") 0o755;
  write_test_file
    root
    "info.vt"
    (Printf.sprintf "\\name \"lit\"\n\\version \"0.1.0\"\n%s\n" default_literate_manifest);
  write_test_file
    root
    "src/a.vt.scrbl"
    "@vt|{\n\
     \\universe U\n\
     \\export id\n\
     \\let id (A : U) : A -> A \\where\n\
    \  <= \\intro\n\
    \  | id A x => x\n\
     }|\n";
  write_test_file
    root
    "src/b.vt.scrbl"
    "@vt|{\n\\import a\n\\universe U\n\\let id2 (A : U) : A -> A => id A\n}|\n";
  match
    weave_file ~explicit_root:root ~scrbl_path:(Filename.concat root "src/b.vt.scrbl") ()
  with
  | None -> false
  | Some (s, _css) ->
    contains s "data-vt-target-file=" && contains s "data-vt-kind=\"use\""
;;

let%test "weave links a local-variable use to its binder occurrence" =
  let dir = Filename.temp_dir "litbinder" "" in
  Unix.mkdir (Filename.concat dir "src") 0o755;
  write_test_file
    dir
    "info.vt"
    (Printf.sprintf "\\name \"lit\"\n\\version \"0.1.0\"\n%s\n" default_literate_manifest);
  write_test_file
    dir
    "src/c.vt.scrbl"
    "@vt|{\n\
     \\universe U\n\
     \\let id (A : U) : A -> A \\where\n\
    \  <= \\intro\n\
    \  | id A x => x\n\
     }|\n";
  match
    weave_file ~explicit_root:dir ~scrbl_path:(Filename.concat dir "src/c.vt.scrbl") ()
  with
  | None -> false
  | Some (s, _css) -> contains s "id=\"vt-loc-"
;;

let%test "weave_project weaves every card under src/, named by its own extension" =
  let tmp = Filename.temp_dir "litproj" "" in
  Unix.mkdir (Filename.concat tmp "src") 0o755;
  write_test_file
    tmp
    "info.vt"
    (Printf.sprintf "\\name \"lit\"\n\\version \"0.1.0\"\n%s\n" default_literate_manifest);
  write_test_file
    tmp
    "src/main.vt.scrbl"
    "@vt|{\n\
     \\universe U\n\
     \\let id (A : U) : A -> A \\where\n\
    \  <= \\intro\n\
    \  | id A x => x\n\
     }|\n";
  let pages, css_paths, failed = weave_project ~root:tmp in
  failed = 0
  && css_paths = []
  &&
  match List.assoc_opt "main.scrbl" pages with
  | Some s -> contains s "data-vt-kind=\"def\""
  | None -> false
;;

let%test "a rule's css attribute writes the stylesheet, project-root-relative" =
  let tmp = Filename.temp_dir "litcss" "" in
  Unix.mkdir (Filename.concat tmp "src") 0o755;
  write_test_file
    tmp
    "info.vt"
    "\\name \"lit\"\n\
     \\version \"0.1.0\"\n\
     \\literate \".scrbl\" (open = \"@vt|{\", close = \"}|\", output = \"cat\", css = \
     \"assets/violet.css\")\n";
  write_test_file tmp "src/f.vt.scrbl" "@vt|{\n\\universe U\n}|\n";
  match
    weave_file ~explicit_root:tmp ~scrbl_path:(Filename.concat tmp "src/f.vt.scrbl") ()
  with
  | None -> false
  | Some (_s, css) -> css = Some (Filename.concat tmp "assets/violet.css")
;;

(* An unterminated code block aborts the weave (returns [None]) instead of
   silently treating the rest of the document as code. *)
let%test "weave aborts on an unterminated block" =
  let dir = Filename.temp_dir "litunterm" "" in
  Unix.mkdir (Filename.concat dir "src") 0o755;
  write_test_file
    dir
    "info.vt"
    (Printf.sprintf "\\name \"lit\"\n\\version \"0.1.0\"\n%s\n" default_literate_manifest);
  write_test_file
    dir
    "src/d.vt.scrbl"
    "@p{intro}\n@vt|{\n\\universe U\n\\let id (A : U) (x : A) : A => x\n";
  weave_file ~explicit_root:dir ~scrbl_path:(Filename.concat dir "src/d.vt.scrbl") ()
  = None
;;

let%test "weave fails clearly when the extension has no \\literate rule" =
  let dir = Filename.temp_dir "litnorule" "" in
  Unix.mkdir (Filename.concat dir "src") 0o755;
  write_test_file dir "info.vt" "\\name \"lit\"\n\\version \"0.1.0\"\n";
  write_test_file dir "src/e.vt.scrbl" "@vt|{\n\\universe U\n}|\n";
  weave_file ~explicit_root:dir ~scrbl_path:(Filename.concat dir "src/e.vt.scrbl") ()
  = None
;;
