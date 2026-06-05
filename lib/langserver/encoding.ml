(** Position encoding conversions at the LSP boundary.

    The LSP protocol's default position encoding is UTF-16: [Position.character]
    counts UTF-16 code units from the start of the line, NOT bytes. Violet's
    interactive index (see {!Violet_interactive.Index}), on the other hand, stores
    {b byte} columns (asai's [offset - start_of_line]).

    Therefore EVERY LSP boundary position must pass through this module:
    - positions arriving from the client (hover/definition/references requests)
      are UTF-16 and must be converted to byte columns before index lookup
      ({!utf16_to_byte});
    - positions/ranges sent back to the client (locations, diagnostics) are byte
      columns and must be converted to UTF-16 ({!byte_to_utf16}).

    On ASCII-only lines the two encodings coincide, so this is a no-op there. The
    conversions only matter on lines containing multi-byte glyphs such as
    [=\xe2\x9f\xa8] (the Violet proof operators [=⟨ ⟩ ∎ ◅ ⍮],
    each 3 UTF-8 bytes / 1 UTF-16 unit). *)

(** [utf16_to_byte ~line_text col] converts a UTF-16 code-unit column [col] into
    a byte column within [line_text].

    Walks the line's UTF-8 with {!String.get_utf_8_uchar}. Each decoded scalar
    value costs [Uchar.utf_16_byte_length u / 2] UTF-16 units (1 for the BMP, 2
    for astral planes). We stop as soon as the running UTF-16 count reaches [col]
    and return the byte index at that point.

    Clamping: a [col] past the end of the line returns the line length.
    Malformed UTF-8 never loops forever: the stdlib decoder always yields a
    replacement decode, and we advance by [Uchar.utf_decode_length]. *)
let utf16_to_byte ~line_text (col : int) : int =
  if col <= 0
  then 0
  else begin
    let len = String.length line_text in
    let byte = ref 0 in
    let utf16 = ref 0 in
    let result = ref None in
    while !result = None && !byte < len do
      if !utf16 >= col
      then result := Some !byte
      else begin
        let dec = String.get_utf_8_uchar line_text !byte in
        let u = Uchar.utf_decode_uchar dec in
        utf16 := !utf16 + (Uchar.utf_16_byte_length u / 2);
        byte := !byte + Uchar.utf_decode_length dec
      end
    done;
    match !result with
    | Some b -> b
    | None -> if !utf16 >= col then !byte else len
  end
;;

(** [byte_to_utf16 ~line_text col] converts a byte column [col] within
    [line_text] into a UTF-16 code-unit column. Inverse of {!utf16_to_byte};
    walks the same way. A [col] past the end of the line returns the line's total
    UTF-16 length. *)
let byte_to_utf16 ~line_text (col : int) : int =
  if col <= 0
  then 0
  else begin
    let len = String.length line_text in
    let target = if col > len then len else col in
    let byte = ref 0 in
    let utf16 = ref 0 in
    while !byte < target do
      let dec = String.get_utf_8_uchar line_text !byte in
      let u = Uchar.utf_decode_uchar dec in
      utf16 := !utf16 + (Uchar.utf_16_byte_length u / 2);
      byte := !byte + Uchar.utf_decode_length dec
    done;
    !utf16
  end
;;

(** [line_text ~doc ~line] extracts the [line]-th (1-based) line of [doc] without
    its trailing newline. Lines beyond end-of-file return [""]. *)
let line_text ~doc ~(line : int) : string =
  if line < 1
  then ""
  else begin
    let len = String.length doc in
    (* Find the byte offset where the requested line starts. *)
    let rec find_start ~pos ~cur =
      if cur = line
      then Some pos
      else if pos >= len
      then None
      else
        begin match String.index_from_opt doc pos '\n' with
        | Some nl -> find_start ~pos:(nl + 1) ~cur:(cur + 1)
        | None -> None (* last line has no trailing newline *)
        end
    in
    match find_start ~pos:0 ~cur:1 with
    | None -> ""
    | Some start ->
      let stop =
        match String.index_from_opt doc start '\n' with
        | Some nl -> nl
        | None -> len
      in
      (* Strip a trailing '\r' for CRLF line endings. *)
      let stop = if stop > start && doc.[stop - 1] = '\r' then stop - 1 else stop in
      String.sub doc start (stop - start)
  end
;;

(* The real proof line "    ((suc m) + n) =\xe2\x9f\xa8 ap suc (add-comm m n) \xe2\x9f\xa9"
   where =\xe2\x9f\xa8 is "=\xe2\x9f\xa8" (U+27E8, 3 bytes / 1 UTF-16 unit) and the trailing
   glyph is U+27E9. Kept as explicit byte escapes so the source stays ASCII. *)
let demo_line = "    ((suc m) + n) =\xe2\x9f\xa8 ap suc (add-comm m n) \xe2\x9f\xa9"

let%expect_test "utf16_to_byte table for the =\xe2\x9f\xa8 proof line" =
  (* For the interesting UTF-16 columns, print (utf16, byte). 'ap' starts at
     UTF-16 col 21, 'suc' at col 24 (after the multibyte =\xe2\x9f\xa8). *)
  List.iter
    (fun u16 -> Printf.printf "%d->%d\n" u16 (utf16_to_byte ~line_text:demo_line u16))
    [ 0; 18; 19; 20; 21; 24; 44; 100 ];
  [%expect
    {|
    0->0
    18->18
    19->19
    20->22
    21->23
    24->26
    44->48
    100->48
    |}]
;;

let%expect_test "byte_to_utf16 round-trips on the proof line" =
  List.iter
    (fun b -> Printf.printf "%d->%d\n" b (byte_to_utf16 ~line_text:demo_line b))
    [ 0; 18; 19; 22; 23; 26; 48 ];
  (* round-trip: utf16 -> byte -> utf16 is identity on the interesting columns *)
  let rt u16 =
    byte_to_utf16 ~line_text:demo_line (utf16_to_byte ~line_text:demo_line u16)
  in
  Printf.printf "rt21=%d rt24=%d rt44=%d\n" (rt 21) (rt 24) (rt 44);
  [%expect
    {|
    0->0
    18->18
    19->19
    22->20
    23->21
    26->24
    48->44
    rt21=21 rt24=24 rt44=44
    |}]
;;

let%expect_test "ASCII line is identity in both directions" =
  let s = "let foo = bar baz" in
  let ok = ref true in
  for c = 0 to String.length s do
    if utf16_to_byte ~line_text:s c <> if c > String.length s then String.length s else c
    then ok := false;
    if byte_to_utf16 ~line_text:s c <> c then ok := false
  done;
  Printf.printf "identity=%b len=%d" !ok (String.length s);
  [%expect {| identity=true len=17 |}]
;;

let%expect_test "astral char costs 2 UTF-16 units / 4 bytes" =
  (* "a" + U+1F600 (grinning face, 4 bytes, 2 UTF-16 units) + "b" *)
  let s = "a\xf0\x9f\x98\x80b" in
  Printf.printf "byte_len=%d\n" (String.length s);
  (* utf16 columns: a=0 emoji=1 (2 units) b=3 *)
  Printf.printf
    "u2b: 0->%d 1->%d 3->%d 4->%d\n"
    (utf16_to_byte ~line_text:s 0)
    (utf16_to_byte ~line_text:s 1)
    (utf16_to_byte ~line_text:s 3)
    (utf16_to_byte ~line_text:s 4);
  Printf.printf
    "b2u: 0->%d 1->%d 5->%d 6->%d\n"
    (byte_to_utf16 ~line_text:s 0)
    (byte_to_utf16 ~line_text:s 1)
    (byte_to_utf16 ~line_text:s 5)
    (byte_to_utf16 ~line_text:s 6);
  [%expect
    {|
    byte_len=6
    u2b: 0->0 1->1 3->5 4->6
    b2u: 0->0 1->1 5->3 6->4
    |}]
;;

let%expect_test "past-end-of-line clamps" =
  let s = "ab" in
  Printf.printf
    "u2b 99=%d b2u 99=%d empty=%d"
    (utf16_to_byte ~line_text:s 99)
    (byte_to_utf16 ~line_text:s 99)
    (utf16_to_byte ~line_text:"" 5);
  [%expect {| u2b 99=2 b2u 99=2 empty=0 |}]
;;

let%expect_test "line_text extracts 1-based lines, clamps past EOF" =
  let doc = "first\nsecond line\nthird\r\n" in
  Printf.printf
    "1=%S 2=%S 3=%S 4=%S 99=%S"
    (line_text ~doc ~line:1)
    (line_text ~doc ~line:2)
    (line_text ~doc ~line:3)
    (line_text ~doc ~line:4)
    (line_text ~doc ~line:99);
  [%expect {| 1="first" 2="second line" 3="third" 4="" 99="" |}]
;;
