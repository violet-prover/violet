(* Orchestrate a literate weave: scan a [*.vt.scrbl] card, elaborate its code
   (project-aware, so cross-card uses resolve), render each block to highlighted
   HTML, and reassemble a [*.scrbl] document that tr-notes renders unchanged. *)

module Loader = Violet_project.Loader
module Index = Violet_interactive.Index
module B = Backend.Tr_notes
module Tty = Asai.Tty.Make (Violet_common.Reporter.Message)

type woven_block =
  { src : string
  ; src_offset : int (* offset in the scrbl document, for diagnostics *)
  ; buf_start : int (* offset in the concatenated code buffer *)
  ; buf_len : int
  }

let read_file (path : string) : string =
  let ic = open_in_bin path in
  Fun.protect ~finally:(fun () -> close_in ic)
  @@ fun () ->
  let n = in_channel_length ic in
  really_input_string ic n
;;

(* Concatenate every block's source into one Violet module buffer, recording
   each block's buffer range so index ranges can be sliced back per block. A
   newline separates blocks so boundaries never fuse two tokens. *)
let build_buffer (segments : Block.segment list) : string * woven_block list =
  let b = Buffer.create 1024 in
  let blocks = ref [] in
  List.iter
    (fun seg ->
       match seg with
       | Block.Verbatim _ -> ()
       | Block.Block { src; src_offset } ->
         let buf_start = Buffer.length b in
         Buffer.add_string b src;
         Buffer.add_char b '\n';
         blocks := { src; src_offset; buf_start; buf_len = String.length src } :: !blocks)
    segments;
  Buffer.contents b, List.rev !blocks
;;

let text_override (filepath : string) : string option =
  if Filename.check_suffix filepath ".vt"
  then (
    let scrbl = filepath ^ ".scrbl" in
    if Sys.file_exists scrbl
    then (
      let _, blocks = build_buffer (Block.scan ~source:scrbl (read_file scrbl)) in
      let b = Buffer.create 256 in
      List.iter
        (fun wb ->
           Buffer.add_string b wb.src;
           Buffer.add_char b '\n')
        blocks;
      Some (Buffer.contents b))
    else None)
  else None
;;

(* Everything one card's source yields once elaborated: the semantic index plus
   the scrbl structure needed to splice highlighted HTML back in. Rendering is
   deferred so the same elaboration can drive both the card's own page and the
   pages of any dependency modules it references (which need the project-wide
   registry, only known after every card is elaborated). *)
type card_elab =
  { entries : Index.entry list
  ; def_paths : (string list, unit) Hashtbl.t
  ; segments : Block.segment list
  ; blocks : woven_block list
  ; module_file : string (* [buffer_source] for the card's own blocks *)
  ; current_addr : string
  ; scrbl_path : string
  ; scan_root : string option (* project root, for the local-card registry *)
  ; dep_roots : (string * string) list (* direct deps, for dep-qualified addrs *)
  }

(* Elaborate one card. Returns [Some elab] on success, or [None] after printing
   elaboration diagnostics (remapped to the scrbl source where possible). *)
let elaborate ?explicit_root ~(scrbl_path : string) () : card_elab option =
  let scrbl_text = read_file scrbl_path in
  let module_file =
    if Filename.check_suffix scrbl_path ".scrbl"
    then Filename.chop_extension scrbl_path
    else scrbl_path
  in
  let current_addr = TRCard.addr_of_path scrbl_path in
  let mode = Loader.mode_for_entry ?explicit_root module_file in
  let scan_root, dep_roots =
    match mode with
    | Loader.Project proj ->
      Some proj.Violet_project.Resolve.root, TRCard.dep_roots_of proj
    | Loader.Single_file _ -> None, []
  in
  let diag_collector = Violet_common.Diagnostic_collector.create () in
  let collector = Violet_interactive.Collector.create () in
  let on_event = Violet_interactive.Collector.on_event collector in
  let aborted = ref false in
  (* Scanning happens inside [Reporter.run] below so an unterminated [@vt|{]
     block reports through the same diagnostic path as elaboration errors,
     rather than escaping as an unhandled effect. *)
  let segments = ref []
  and blocks = ref [] in
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
          let segs = Block.scan ~source:scrbl_path scrbl_text in
          segments := segs;
          let buffer, blks = build_buffer segs in
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
    let scrbl_off_of buf_off =
      List.find_opt
        (fun wb -> buf_off >= wb.buf_start && buf_off < wb.buf_start + wb.buf_len)
        !blocks
      |> Option.map (fun wb -> wb.src_offset + (buf_off - wb.buf_start))
    in
    (* Re-anchor each diagnostic onto the scrbl document so [Tty.display]
       highlights the real source, like [violet check]. Elaboration errors
       arrive pointing into the synthesized code buffer; scan errors already
       point into the scrbl. A loc that maps nowhere is dropped (the message
       still renders without a snippet). *)
    let scrbl_loc (d : Violet_common.Reporter.Message.t Asai.Diagnostic.t)
      : Asai.Range.t option
      =
      match d.explanation.loc with
      | None -> None
      | Some loc ->
        (match Violet_common.Range.source loc with
         | Some s when String.equal s scrbl_path -> Some loc
         | Some s when String.equal s module_file ->
           (match scrbl_off_of (Violet_common.Range.start_offset loc) with
            | Some soff ->
              let w = Violet_common.Range.width loc in
              let len = String.length scrbl_text in
              (* Within a block, buffer offsets map to scrbl offsets by a
                 constant shift, so the span width carries over. Guard against
                 the [End_of_file] sentinel ([width = max_int]). *)
              let e = if w >= 0 && w <= len - soff then soff + w else soff in
              Some (Block.range_of ~source:scrbl_path scrbl_text soff e)
            | None -> None)
         | _ -> None)
    in
    List.iter
      (fun (d : Violet_common.Reporter.Message.t Asai.Diagnostic.t) ->
         let loc = scrbl_loc d in
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
      ; current_addr
      ; scrbl_path
      ; scan_root
      ; dep_roots
      }
  end
;;

(* Splice highlighted HTML back into the card's scrbl prose. *)
let render_card (e : card_elab) ~(registry : TRCard.t) : string =
  let out = Buffer.create 1024 in
  let blk_q = ref e.blocks in
  List.iter
    (fun seg ->
       match seg with
       | Block.Verbatim s -> Buffer.add_string out (B.passthrough s)
       | Block.Block _ ->
         let wb = List.hd !blk_q in
         blk_q := List.tl !blk_q;
         let html =
           Highlight.render
             ~src:wb.src
             ~buf_offset:wb.buf_start
             ~buffer_source:e.module_file
             ~entries:e.entries
             ~current_addr:e.current_addr
             ~registry
             ~def_paths:e.def_paths
         in
         Buffer.add_string out (B.wrap_block html))
    e.segments;
  Buffer.contents out
;;

(* A self-contained HTML page. Dependency pages cannot go through tr-notes: they
   carry no scribble prose (just one highlighted block), and their slash-bearing
   addr ([std/id]) is one tr-notes flattens to a bare stem, mis-routing the page.
   So weave emits the final HTML itself, linking the shared stylesheet by an
   absolute path (it sits at the site root, served as [/violet.css]). *)
let standalone_html ~(addr : string) ~(body : string) : string =
  Printf.sprintf
    "<!DOCTYPE html>\n\
     <html lang=\"en\">\n\
     <head>\n\
     <meta charset=\"utf-8\">\n\
     <title>%s</title>\n\
     <link rel=\"stylesheet\" href=\"/violet.css\">\n\
     </head>\n\
     <body>\n\
     <pre>%s</pre>\n\
     </body>\n\
     </html>\n"
    addr
    body
;;

(* Render a dependency module's whole [.vt] source as a single highlighted page.
   [src] is the dep file's path (matching the [Range.source] of its index
   entries), [addr] its dep-qualified card address (e.g. [std/id]). The result is
   a complete HTML document, not a scrbl fragment — see [standalone_html]. *)
let render_dep_page
      (e : card_elab)
      ~(registry : TRCard.t)
      ~(addr : string)
      ~(src : string)
  : string
  =
  let text = read_file src in
  let html =
    Highlight.render
      ~src:text
      ~buf_offset:0
      ~buffer_source:src
      ~entries:e.entries
      ~current_addr:addr
      ~registry
      ~def_paths:e.def_paths
  in
  standalone_html ~addr ~body:html
;;

(* Relative output path for a woven page, keyed off its address. A dependency
   address is slash-bearing ([std/id]); it becomes [<addr>/index.html] so the
   cross-package URL [/<addr>] resolves by directory index — matching how
   tr-notes serves cards and avoiding a dependence on the host adding [.html]. A
   card address is a bare stem and stays [<addr>.scrbl] for tr-notes to render. *)
let output_path ~(addr : string) : string =
  if String.contains addr '/' then Filename.concat addr "index.html" else addr ^ ".scrbl"
;;

(* The distinct dependency modules this elaboration references through a [Use],
   as [(dep-addr, dep-source)] pairs (e.g. [("std/id", ".../std/src/id.vt")]).
   One elaboration already pulls in the whole import closure, so even a
   single-card weave sees every dependency it actually uses. *)
let referenced_dep_pages (e : card_elab) (registry : TRCard.t) : (string * string) list =
  let seen = Hashtbl.create 8 in
  List.filter_map
    (fun (en : Index.entry) ->
       match en.kind, en.def_target with
       | Index.Use, Some loc ->
         (match Violet_common.Range.source loc with
          | Some src ->
            (match TRCard.dep_addr_of_source registry src with
             | Some daddr when not (Hashtbl.mem seen daddr) ->
               Hashtbl.add seen daddr ();
               Some (daddr, src)
             | _ -> None)
          | None -> None)
       | _ -> None)
    e.entries
;;

(* Weave one card. Returns [Some (card-scrbl, dep-pages)] on success, or [None]
   after printing elaboration diagnostics. [dep-pages] are [(addr, html)] for the
   self-contained pages of the dependency modules this card uses; they let the
   per-card weave emit cross-package targets inline, with no separate whole-project
   pass. The registry knows the project's local cards (so cross-card jumps resolve)
   and the referenced dep pages (so cross-package uses link). *)
let weave_file ?explicit_root ~(scrbl_path : string) ()
  : (string * (string * string) list) option
  =
  match elaborate ?explicit_root ~scrbl_path () with
  | None -> None
  | Some e ->
    let registry =
      match e.scan_root with
      | Some root -> TRCard.scan ~dep_roots:e.dep_roots ~root
      | None -> TRCard.empty ()
    in
    (* Always know about the card being woven, so its own in-page jumps resolve
       even in single-file mode. *)
    TRCard.add registry ~addr:e.current_addr ~path:e.scrbl_path;
    let deps = referenced_dep_pages e registry in
    (* Register each referenced dep page before rendering, so cross-package uses
       resolve to a link instead of an unlinked token. *)
    List.iter (fun (addr, src) -> TRCard.add registry ~addr ~path:src) deps;
    let dep_pages =
      List.map (fun (addr, src) -> addr, render_dep_page e ~registry ~addr ~src) deps
    in
    Some (render_card e ~registry, dep_pages)
;;

(* Weave every card under [<root>/src], plus a page for each dependency module
   actually referenced. Returns [(addr, output)] pairs — dep pages carry a
   slash-bearing addr like [std/id] — and the count of cards that failed to
   elaborate. Dependency pages are emitted only for modules whose definitions are
   *used*: a single elaboration's index already contains the full transitive set
   of dep-module uses (every imported module is elaborated), so scanning all uses
   yields the referenced closure without a second pass. *)
let weave_project ~(root : string) : (string * string) list * int =
  let proj =
    try Some (Violet_project.Resolve.load root) with
    | Violet_project.Resolve.Project_error _ -> None
  in
  let dep_roots =
    match proj with
    | Some p -> TRCard.dep_roots_of p
    | None -> []
  in
  let local = TRCard.scan ~dep_roots ~root in
  let cards = TRCard.cards local in
  let failed = ref 0 in
  let elabs =
    List.filter_map
      (fun (addr, scrbl_path) ->
         match elaborate ~explicit_root:root ~scrbl_path () with
         | Some e -> Some (addr, e)
         | None ->
           incr failed;
           None)
      cards
  in
  (* Dep module -> (its source path, an elab whose index covers it). Any card
     that reaches the module elaborated it fully, so either elab renders it. *)
  let referenced : (string, string * card_elab) Hashtbl.t = Hashtbl.create 16 in
  List.iter
    (fun (_addr, e) ->
       List.iter
         (fun (en : Index.entry) ->
            match en.kind, en.def_target with
            | Index.Use, Some loc ->
              (match Violet_common.Range.source loc with
               | Some src ->
                 (match TRCard.dep_addr_of_source local src with
                  | Some daddr ->
                    if not (Hashtbl.mem referenced daddr)
                    then Hashtbl.replace referenced daddr (src, e)
                  | None -> ())
               | None -> ())
            | _ -> ())
         e.entries)
    elabs;
  (* Final registry: local cards + every referenced dep module, so card->dep and
     dep->dep links resolve and nothing points at an unemitted page. *)
  let registry = TRCard.scan ~dep_roots ~root in
  Hashtbl.iter (fun addr (src, _) -> TRCard.add registry ~addr ~path:src) referenced;
  let card_pages = List.map (fun (addr, e) -> addr, render_card e ~registry) elabs in
  let dep_pages =
    Hashtbl.fold
      (fun addr (src, e) acc -> (addr, render_dep_page e ~registry ~addr ~src) :: acc)
      referenced
      []
  in
  card_pages @ dep_pages, !failed
;;

let contains (s : string) (sub : string) : bool =
  let n = String.length s
  and m = String.length sub in
  let rec go i = i + m <= n && (String.equal (String.sub s i m) sub || go (i + 1)) in
  go 0
;;

let%test "weave resolves in-page and cross-card goto-definition" =
  let root = Filename.temp_dir "litweave" "" in
  Unix.mkdir (Filename.concat root "src") 0o755;
  let write rel content =
    let oc = open_out (Filename.concat root rel) in
    output_string oc content;
    close_out oc
  in
  write "info.vt" "\\name \"lit\"\n\\version \"0.1.0\"\n";
  write
    "src/a.vt.scrbl"
    "@p{a}\n\
     @vt|{\n\
     \\universe U\n\
     \\export id\n\
     \\let id (A : U) : A -> A \\where\n\
    \  <= \\intro\n\
    \  | id A x => x\n\
     }|\n";
  write
    "src/b.vt.scrbl"
    "@p{b}\n@vt|{\n\\import a\n\\universe U\n\\let id2 (A : U) : A -> A => id A\n}|\n";
  match
    weave_file ~explicit_root:root ~scrbl_path:(Filename.concat root "src/b.vt.scrbl") ()
  with
  | None -> false
  | Some (s, _deps) ->
    contains s "@pre|{"
    && contains s "id=\"vt-def-b/id2\""
    && contains s "href=\"/a#vt-def-a/id\""
;;

(* A use of a local variable [x] links to its binder occurrence, addressed by
   offset (binders are not unique by name). Single-file mode: the card registers
   itself, so its addr (here the temp basename) is known. *)
let%test "weave links a local-variable use to its binder occurrence" =
  let dir = Filename.temp_dir "litbinder" "" in
  let path = Filename.concat dir "c.vt.scrbl" in
  let oc = open_out path in
  output_string
    oc
    "@vt|{\n\
     \\universe U\n\
     \\let id (A : U) : A -> A \\where\n\
    \  <= \\intro\n\
    \  | id A x => x\n\
     }|\n";
  close_out oc;
  match weave_file ~scrbl_path:path () with
  | None -> false
  | Some (s, _deps) ->
    (* a binder-targeting href exists, and a matching binder id is emitted *)
    contains s "#vt-loc-c-" && contains s "id=\"vt-loc-c-"
;;

(* A whole-project weave emits a page for each *referenced* dependency module,
   addressed by its dep key (here [std/id]), and the consumer card links into
   it. The dep page's own definition carries the matching anchor id, so the
   cross-package jump resolves. *)
let%test "weave_project emits a page for a referenced dependency module" =
  let tmp = Filename.temp_dir "litdep" "" in
  let write rel content =
    let path = Filename.concat tmp rel in
    let dir = Filename.dirname path in
    if not (Sys.file_exists dir) then Unix.mkdir dir 0o755;
    let oc = open_out path in
    output_string oc content;
    close_out oc
  in
  (* dependency project: a plain .vt module exporting [id] *)
  Unix.mkdir (Filename.concat tmp "std") 0o755;
  write "std/info.vt" "\\name \"std\"\n\\version \"0.1.0\"\n";
  write
    "std/src/id.vt"
    "\\universe U\n\
     \\export id\n\
     \\let id (A : U) : A -> A \\where\n\
    \  <= \\intro\n\
    \  | id A x => x\n";
  (* consumer project: a card that imports and uses [std/id] *)
  Unix.mkdir (Filename.concat tmp "app") 0o755;
  write
    "app/info.vt"
    "\\name \"app\"\n\\version \"0.1.0\"\n\\dep std (path = \"../std\")\n";
  write
    "app/src/main.vt.scrbl"
    "@p{m}\n\
     @vt|{\n\
     \\import std/id\n\
     \\universe U\n\
     \\let id2 (A : U) : A -> A => id A\n\
     }|\n";
  let pages, failed = weave_project ~root:(Filename.concat tmp "app") in
  failed = 0
  (* the dep module got its own self-contained HTML page served at a directory
     index, with the def anchor the consumer targets *)
  && String.equal (output_path ~addr:"std/id") "std/id/index.html"
  && (match List.assoc_opt "std/id" pages with
      | Some html ->
        contains html "id=\"vt-def-std/id/id\""
        && contains html "<link rel=\"stylesheet\" href=\"/violet.css\">"
      | None -> false)
  (* the consumer card is a scrbl that links across the package boundary *)
  && String.equal (output_path ~addr:"main") "main.scrbl"
  &&
  match List.assoc_opt "main" pages with
  | Some html -> contains html "href=\"/std/id#vt-def-std/id/id\""
  | None -> false
;;

(* A single-card weave produces the dependency pages it uses, inline — no
   separate whole-project pass. The card links across the package boundary and
   the returned dep page carries the matching anchor and its own stylesheet link,
   so emitting it as [std/id/index.html] makes the jump resolve. *)
let%test "weave_file emits the dependency pages a card uses" =
  let tmp = Filename.temp_dir "litdepfile" "" in
  let write rel content =
    let path = Filename.concat tmp rel in
    let dir = Filename.dirname path in
    if not (Sys.file_exists dir) then Unix.mkdir dir 0o755;
    let oc = open_out path in
    output_string oc content;
    close_out oc
  in
  Unix.mkdir (Filename.concat tmp "std") 0o755;
  write "std/info.vt" "\\name \"std\"\n\\version \"0.1.0\"\n";
  write
    "std/src/id.vt"
    "\\universe U\n\
     \\export id\n\
     \\let id (A : U) : A -> A \\where\n\
    \  <= \\intro\n\
    \  | id A x => x\n";
  Unix.mkdir (Filename.concat tmp "app") 0o755;
  write
    "app/info.vt"
    "\\name \"app\"\n\\version \"0.1.0\"\n\\dep std (path = \"../std\")\n";
  write
    "app/src/main.vt.scrbl"
    "@p{m}\n\
     @vt|{\n\
     \\import std/id\n\
     \\universe U\n\
     \\let id2 (A : U) : A -> A => id A\n\
     }|\n";
  match
    weave_file
      ~explicit_root:(Filename.concat tmp "app")
      ~scrbl_path:(Filename.concat tmp "app/src/main.vt.scrbl")
      ()
  with
  | None -> false
  | Some (card, dep_pages) ->
    (* the card links across the boundary *)
    contains card "href=\"/std/id#vt-def-std/id/id\""
    (* and the very same weave handed back the dep page that link targets *)
    &&
      (match List.assoc_opt "std/id" dep_pages with
      | Some html ->
        contains html "id=\"vt-def-std/id/id\""
        && contains html "<link rel=\"stylesheet\" href=\"/violet.css\">"
      | None -> false)
;;

(* An unterminated [@vt|{] block aborts the weave (returns [None]) instead of
   silently treating the rest of the document as code. The exact rendered
   diagnostic (loc + message) is pinned by the literate/bad fixture golden in
   test_violet; here we only assert the end-to-end abort. *)
let%test "weave aborts on an unterminated @vt block" =
  let dir = Filename.temp_dir "litunterm" "" in
  let path = Filename.concat dir "d.vt.scrbl" in
  let oc = open_out path in
  output_string oc "@p{intro}\n@vt|{\n\\universe U\n\\let id (A : U) (x : A) : A => x\n";
  close_out oc;
  weave_file ~scrbl_path:path () = None
;;
