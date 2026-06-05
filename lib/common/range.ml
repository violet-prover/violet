(* Utilities on [Asai.Range.t], shared by surface, elab, interactive and
   the language server. *)

(* The range from [a]'s start to [b]'s end. Locations on synthesized terms
   are provenance tags, so [a] and [b] may come from different sources or
   appear in either textual order; joining is only meaningful for
   same-source ranges with [a] starting no later than [b] ends. Everything
   else (including EOF views) falls back to [a]. *)
let join (a : Asai.Range.t) (b : Asai.Range.t) : Asai.Range.t =
  match Asai.Range.view a, Asai.Range.view b with
  | `Range (s, _), `Range (_, e) when s.source = e.source && s.offset <= e.offset ->
    Asai.Range.make (s, e)
  | _ -> a
;;

(* For whitebox tests and the REPL, where there is no source file. *)
let dummy : Asai.Range.t = Asai.Range.of_lex_range (Lexing.dummy_pos, Lexing.dummy_pos)

let start_offset (r : Asai.Range.t) : int =
  match Asai.Range.view r with
  | `Range (s, _) -> s.offset
  | `End_of_file p -> p.offset
;;

(* The file a range points into; [None] for in-memory (`String) sources. *)
let source (r : Asai.Range.t) : string option =
  match Asai.Range.view r with
  | `Range (s, _) ->
    (match s.source with
     | `File f -> Some f
     | `String _ -> None)
  | `End_of_file s ->
    (match s.source with
     | `File f -> Some f
     | `String _ -> None)
;;

let is_multiline (r : Asai.Range.t) : bool =
  match Asai.Range.view r with
  | `Range (s, e) -> s.line_num <> e.line_num
  | `End_of_file _ -> false
;;

let pos_in_range ~line ~col (r : Asai.Range.t) : bool =
  match Asai.Range.view r with
  | `Range (s, e) ->
    let s_col = s.offset - s.start_of_line in
    let e_col = e.offset - e.start_of_line in
    (line > s.line_num || (line = s.line_num && col >= s_col))
    && (line < e.line_num || (line = e.line_num && col <= e_col))
  | `End_of_file _ -> false
;;

let width (r : Asai.Range.t) : int =
  match Asai.Range.view r with
  | `Range (s, e) -> e.offset - s.offset
  | `End_of_file _ -> max_int
;;

(* join is fed provenance locs on synthesized terms, which come in
   arbitrary textual order and possibly from different files. It must be
   total: out-of-order or cross-source pairs fall back to the first range
   instead of raising (Asai.Range.make asserts start <= end). *)
let%expect_test "join: ordered, inverted, cross-file" =
  let mk_range file b e : Asai.Range.t =
    let pos cnum : Lexing.position =
      { pos_fname = file; pos_lnum = 1; pos_bol = 0; pos_cnum = cnum }
    in
    Asai.Range.of_lex_range (pos b, pos e)
  in
  let show r =
    match Asai.Range.view r with
    | `Range (s, e) -> Printf.sprintf "[%d,%d)" s.Asai.Range.offset e.Asai.Range.offset
    | `End_of_file _ -> "<eof>"
  in
  let early = mk_range "f.vt" 10 20 in
  let late = mk_range "f.vt" 50 60 in
  let other = mk_range "g.vt" 0 5 in
  Printf.printf
    "ordered=%s inverted=%s cross=%s"
    (show (join early late))
    (show (join late early))
    (show (join early other));
  [%expect {| ordered=[10,60) inverted=[50,60) cross=[10,20) |}]
;;
