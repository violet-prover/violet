(* Shared literate preprocessing.

   A [*.vt.scrbl] card is a scribble document with Violet code in [@vt|{}|]
   blocks. Both the weaver and the language server need to (1) synthesize a
   single Violet module buffer from the card's blocks so the existing parser and
   elaborator run unchanged, and (2) map byte offsets in that synthesized buffer
   back onto the original scrbl document so diagnostics and index ranges point at
   real source. That two-way bridge lives here so the two callers cannot diverge. *)

type woven_block =
  { src : string (* the Violet code between [|{] and [}|] *)
  ; src_offset : int (* offset of [src] within the scrbl document *)
  ; buf_start : int (* offset of [src] within the synthesized buffer *)
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
   each block's buffer range so offsets can be sliced back per block. A newline
   separates blocks so boundaries never fuse two tokens. *)
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

(* Scan a scrbl document and synthesize its module buffer in one step. Runs
   under the ambient [Reporter] so an unterminated [@vt|{] block reports through
   the same diagnostic path as elaboration errors. *)
let to_buffer ~(source : string) (scrbl_text : string)
  : Block.segment list * string * woven_block list
  =
  let segs = Block.scan ~source scrbl_text in
  let buffer, blocks = build_buffer segs in
  segs, buffer, blocks
;;

(* Map a synthesized-buffer byte offset to its scrbl byte offset, if it lands
   inside a block. *)
let scrbl_offset_of (blocks : woven_block list) (buf_off : int) : int option =
  List.find_opt
    (fun wb -> buf_off >= wb.buf_start && buf_off < wb.buf_start + wb.buf_len)
    blocks
  |> Option.map (fun wb -> wb.src_offset + (buf_off - wb.buf_start))
;;

(* Re-anchor a range onto the scrbl document. *)
let remap_range
      ~(blocks : woven_block list)
      ~(scrbl_path : string)
      ~(scrbl_text : string)
      ~(module_file : string)
      (loc : Asai.Range.t)
  : Asai.Range.t option
  =
  match Violet_common.Range.source loc with
  | Some s when String.equal s scrbl_path -> Some loc
  | Some s when String.equal s module_file ->
    (match scrbl_offset_of blocks (Violet_common.Range.start_offset loc) with
     | Some soff ->
       let w = Violet_common.Range.width loc in
       let len = String.length scrbl_text in
       (* Guard against the [End_of_file] sentinel ([width = max_int]). *)
       let e = if w >= 0 && w <= len - soff then soff + w else soff in
       Some (Block.range_of ~source:scrbl_path scrbl_text soff e)
     | None -> None)
  | _ -> None
;;
