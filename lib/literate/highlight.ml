module L = Violet_surface.Lexer
module LT = Violet_surface.Lexer_tokens
module Index = Violet_interactive.Index

let range_start = Violet_common.Range.start_offset

let range_end (r : Asai.Range.t) : int =
  let w = Violet_common.Range.width r in
  if w = max_int then range_start r else range_start r + w
;;

let hl_range (e : Index.entry) : Asai.Range.t =
  match e.kind with
  | Index.Def -> Option.value e.def_loc ~default:e.loc
  | _ -> e.loc
;;

(* A definition's stable id, so an output hook that wants same-document jump
   links can build them itself by matching a [Use]'s [data-vt-path] against a
   [Def]'s [id]. Not addr-qualified: each weave run renders one file's worth
   of blocks into one output document (or, for a whole-project weave, each
   card is its own separate output file), so a path is already unique within
   the scope any single hook invocation's output lands in — no cross-card
   transclusion concept survives here; that was tr-notes-specific and is now
   the hook's problem, not Violet's. *)
let anchor_id (path : string list) : string = "vt-def-" ^ String.concat "/" path

(* A local-variable binder's jump target, keyed by byte offset (names are not
   unique) within the current file — see [binder_targets]. *)
let loc_anchor_id (offset : int) : string = Printf.sprintf "vt-loc-%d" offset

let escape (s : string) : string =
  let b = Buffer.create (String.length s) in
  String.iter
    (fun c ->
       match c with
       | '&' -> Buffer.add_string b "&amp;"
       | '<' -> Buffer.add_string b "&lt;"
       | '>' -> Buffer.add_string b "&gt;"
       | '"' -> Buffer.add_string b "&quot;"
       | c -> Buffer.add_char b c)
    s;
  Buffer.contents b
;;

let kw_class (t : L.token) : string option =
  match t with
  | L.DATA
  | L.LET
  | L.EXPORT
  | L.IMPORT
  | L.UNIVERSE
  | L.WHERE
  | L.OPERATOR
  | L.OPEN
  | L.ELIM
  | L.INTRO
  | L.SPLIT
  | L.STRONGER_THAN
  | L.WEAKER_THAN
  | L.SAME_AS
  | L.ASSOCIATIVITY
  | L.LEFT
  | L.RIGHT
  | L.NONE
  | L.RECORD
  | L.WITH
  | L.AXIOM
  | L.LAMBDA -> Some "vt-kw"
  | L.ARROW
  | L.STACK_ARROW
  | L.FAT_ARROW
  | L.COLON
  | L.SLASH
  | L.VERT
  | L.JOIN
  | L.DOT
  | L.QMARK
  | L.SYMBOL _ -> Some "vt-op"
  | L.L_PAREN | L.R_PAREN | L.L_BRACKET | L.R_BRACKET -> Some "vt-punct"
  | L.STRING _ -> Some "vt-str"
  | L.IDENT _ -> None (* plain unless an index entry covers it *)
  | L.EOF -> None
;;

let tip (body : string) : string =
  if String.equal body "" then "" else "<span class=\"vt-tip\">" ^ escape body ^ "</span>"
;;

let type_tip (e : Index.entry) : string =
  match e.pp_ty with
  | Some t -> tip t
  | None -> ""
;;

let goal_tip (e : Index.entry) : string =
  let ctx = List.map (fun (n, t) -> n ^ " : " ^ t) e.ctx in
  let target =
    match e.pp_target with
    | Some t -> [ "\xe2\x8a\xa2 " ^ t ] (* "⊢ " *)
    | None -> []
  in
  tip (String.concat "\n" (ctx @ target))
;;

let data_attr name value = Printf.sprintf " data-vt-%s=\"%s\"" name (escape value)

let data_attr_opt name = function
  | None -> ""
  | Some v -> data_attr name v
;;

(* Raw resolution info for a [Use]: which file its target lives in and where
   in that file — works identically whether the target is local, elsewhere in
   the project, or in a dependency. An output hook decides what, if anything,
   to do with this (build its own cross-file link scheme, show a tooltip,
   ignore it); Violet no longer assumes any URL scheme. *)
let target_info (e : Index.entry) : (string * int) option =
  match e.def_target with
  | None -> None
  | Some loc ->
    (match Violet_common.Range.source loc with
     | None -> None
     | Some path -> Some (path, range_start loc))
;;

let render_semantic ?(loc_id = None) (e : Index.entry) (text : string) : string =
  let et = escape text in
  let id_attr =
    match loc_id with
    | Some a -> Printf.sprintf " id=\"%s\"" a
    | None -> ""
  in
  let path_str = if e.path = [] then None else Some (String.concat "/" e.path) in
  match e.kind with
  | Index.Def ->
    Printf.sprintf
      "<span class=\"vt-def\" id=\"%s\"%s%s>%s%s</span>"
      (anchor_id e.path)
      (data_attr "kind" "def")
      (data_attr_opt "type" e.pp_ty)
      et
      (type_tip e)
  | Index.Binder ->
    Printf.sprintf
      "<span class=\"vt-binder\"%s%s%s>%s%s</span>"
      id_attr
      (data_attr "kind" "binder")
      (data_attr_opt "type" e.pp_ty)
      et
      (type_tip e)
  | Index.Use ->
    let target_attrs =
      match target_info e with
      | Some (path, off) ->
        data_attr "target-file" path ^ data_attr "target-offset" (string_of_int off)
      | None -> ""
    in
    Printf.sprintf
      "<span class=\"vt-use\"%s%s%s%s%s>%s%s</span>"
      id_attr
      (data_attr "kind" "use")
      (data_attr_opt "path" path_str)
      (data_attr_opt "type" e.pp_ty)
      target_attrs
      et
      (type_tip e)
  | Index.Goal ->
    Printf.sprintf
      "<span class=\"vt-goal\"%s>%s%s</span>"
      (data_attr "kind" "goal")
      et
      (goal_tip e)
;;

(* Buffer offsets that some local-variable use points at (its binding site).
   The entry rendered at such an offset must carry the matching [id] so an
   output hook can build the jump, regardless of whether a Binder or a Use is
   selected there. *)
let binder_targets ~buffer_source ~def_paths (entries : Index.entry list)
  : (int, unit) Hashtbl.t
  =
  let tbl = Hashtbl.create 32 in
  List.iter
    (fun (e : Index.entry) ->
       match e.kind, e.def_target with
       | Index.Use, Some loc when not (Hashtbl.mem def_paths e.path) ->
         (match Violet_common.Range.source loc with
          | Some s when String.equal s buffer_source ->
            Hashtbl.replace tbl (range_start loc) ()
          | _ -> ())
       | _ -> ())
    entries;
  tbl
;;

let build_entry_map ~buffer_source ~buf_offset ~src_len (entries : Index.entry list)
  : (int, Index.entry) Hashtbl.t
  =
  let lo = buf_offset
  and hi = buf_offset + src_len in
  let tbl = Hashtbl.create 64 in
  let width (e : Index.entry) = range_end (hl_range e) - range_start (hl_range e) in
  let better a b =
    width a < width b
    || (width a = width b && b.Index.kind = Index.Binder && a.Index.kind <> Index.Binder)
  in
  List.iter
    (fun (e : Index.entry) ->
       let same_src =
         match Violet_common.Range.source (hl_range e) with
         | Some s -> String.equal s buffer_source
         | None -> false
       in
       if same_src
       then begin
         let s = range_start (hl_range e) in
         if s >= lo && s < hi
         then (
           match Hashtbl.find_opt tbl s with
           | None -> Hashtbl.replace tbl s e
           | Some prev -> if better e prev then Hashtbl.replace tbl s e)
       end)
    entries;
  tbl
;;

let render
      ~(src : string)
      ~(buf_offset : int)
      ~(buffer_source : string)
      ~(entries : Index.entry list)
      ~(def_paths : (string list, unit) Hashtbl.t)
  : string
  =
  let entry_map =
    build_entry_map ~buffer_source ~buf_offset ~src_len:(String.length src) entries
  in
  let targets = binder_targets ~buffer_source ~def_paths entries in
  let loc_id_at buf_off =
    if Hashtbl.mem targets buf_off then Some (loc_anchor_id buf_off) else None
  in
  let toks = Array.of_list (LT.tokens_with_spans src) in
  let n = Array.length toks in
  let out = Buffer.create (String.length src * 2) in
  let cursor = ref 0 in
  let slice a b = String.sub src a (b - a) in
  let i = ref 0 in
  while !i < n do
    let tk = toks.(!i) in
    if tk.LT.start_offset > !cursor
    then Buffer.add_string out (escape (slice !cursor tk.LT.start_offset));
    let buf_off = buf_offset + tk.LT.start_offset in
    match Hashtbl.find_opt entry_map buf_off with
    | Some e ->
      let e_end_local = min (String.length src) (range_end (hl_range e) - buf_offset) in
      let seg_end =
        if e_end_local > tk.LT.start_offset then e_end_local else tk.LT.end_offset
      in
      Buffer.add_string
        out
        (render_semantic ~loc_id:(loc_id_at buf_off) e (slice tk.LT.start_offset seg_end));
      cursor := seg_end;
      incr i;
      while !i < n && toks.(!i).LT.end_offset <= seg_end do
        incr i
      done
    | None ->
      let text = slice tk.LT.start_offset tk.LT.end_offset in
      let body =
        match kw_class tk.LT.token with
        | Some cls -> Printf.sprintf "<span class=\"%s\">%s</span>" cls (escape text)
        | None -> escape text
      in
      (* a binder occurrence with no semantic entry of its own still needs its
         jump target id *)
      (match loc_id_at buf_off with
       | Some a ->
         Buffer.add_string out (Printf.sprintf "<span id=\"%s\">%s</span>" a body)
       | None -> Buffer.add_string out body);
      cursor := tk.LT.end_offset;
      incr i
  done;
  if !cursor < String.length src
  then Buffer.add_string out (escape (slice !cursor (String.length src)));
  Buffer.contents out
;;
