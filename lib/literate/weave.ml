(* Orchestrate a literate weave: scan a [*.vt.scrbl] card, elaborate its code
   (project-aware, so cross-card uses resolve), render each block to highlighted
   HTML, and reassemble a [*.scrbl] document that tr-notes renders unchanged. *)

module Loader = Violet_project.Loader
module Index = Violet_interactive.Index
module B = Backend.Tr_notes

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

let line_col (text : string) (off : int) : int * int =
  let line = ref 1
  and col = ref 1 in
  let off = min off (String.length text) in
  for k = 0 to off - 1 do
    if text.[k] = '\n'
    then begin
      incr line;
      col := 1
    end
    else incr col
  done;
  !line, !col
;;

let message_of (d : Violet_common.Reporter.Message.t Asai.Diagnostic.t) : string =
  let buf = Buffer.create 128 in
  let fmt = Format.formatter_of_buffer buf in
  Format.fprintf fmt "%t" d.explanation.value;
  Format.pp_print_flush fmt ();
  Buffer.contents buf
;;

let text_override (filepath : string) : string option =
  if Filename.check_suffix filepath ".vt"
  then (
    let scrbl = filepath ^ ".scrbl" in
    if Sys.file_exists scrbl
    then (
      let _, blocks = build_buffer (Block.scan (read_file scrbl)) in
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

(* Weave one card. Returns [Some output] on success, or [None] after printing
   elaboration diagnostics (remapped to the scrbl source where possible). *)
let weave_file ?explicit_root ~(scrbl_path : string) () : string option =
  let scrbl_text = read_file scrbl_path in
  let segments = Block.scan scrbl_text in
  let buffer, blocks = build_buffer segments in
  let module_file =
    if Filename.check_suffix scrbl_path ".scrbl"
    then Filename.chop_extension scrbl_path
    else scrbl_path
  in
  let current_addr = TRCard.addr_of_path scrbl_path in
  let mode = Loader.mode_for_entry ?explicit_root module_file in
  let registry =
    match mode with
    | Loader.Project proj -> TRCard.scan ~root:proj.Violet_project.Resolve.root
    | Loader.Single_file _ -> TRCard.empty ()
  in
  (* Always know about the card being woven, so its own in-page jumps resolve
     even in single-file mode. *)
  TRCard.add registry ~addr:current_addr ~path:scrbl_path;
  let diag_collector = Violet_common.Diagnostic_collector.create () in
  let collector = Violet_interactive.Collector.create () in
  let on_event = Violet_interactive.Collector.on_event collector in
  let aborted = ref false in
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
                 let mp = String.split_on_char '/' mn in
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
        blocks
      |> Option.map (fun wb -> wb.src_offset + (buf_off - wb.buf_start))
    in
    List.iter
      (fun d ->
         let msg = message_of d in
         match d.Asai.Diagnostic.explanation.loc with
         | Some loc
           when match Violet_common.Range.source loc with
                | Some s -> String.equal s module_file
                | None -> false ->
           (match scrbl_off_of (Violet_common.Range.start_offset loc) with
            | Some soff ->
              let l, c = line_col scrbl_text soff in
              Printf.eprintf "%s:%d:%d: error: %s\n" scrbl_path l c msg
            | None -> Printf.eprintf "%s: error: %s\n" scrbl_path msg)
         | _ -> Printf.eprintf "%s: error: %s\n" scrbl_path msg)
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
    let out = Buffer.create (String.length scrbl_text * 2) in
    let blk_q = ref blocks in
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
               ~buffer_source:module_file
               ~entries
               ~current_addr
               ~registry
               ~def_paths
           in
           Buffer.add_string out (B.wrap_block html))
      segments;
    Some (Buffer.contents out)
  end
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
  | Some s ->
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
  | Some s ->
    (* a binder-targeting href exists, and a matching binder id is emitted *)
    contains s "#vt-loc-c-" && contains s "id=\"vt-loc-c-"
;;
