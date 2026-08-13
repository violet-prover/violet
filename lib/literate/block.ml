(* Scan a literate document into verbatim prose and Violet code blocks.

   A code block is bracketed by a caller-supplied [Delim.t]: the literal
   [open_] and [close] tokens, e.g. the scrbl pipe-brace form [@vt|{ ... }|]
   ([Delim.scrbl]), or any other comment-safe token pair a host document
   format offers. Everything between [open_] and the next occurrence of
   [close] is passed through as Violet source verbatim; the [close] string
   must therefore not occur literally inside a block's own source (for
   [Delim.scrbl] this is [}|]; the highlighter additionally escapes [|] in
   its generated output so it can never produce that sequence).

   This is a purely textual pre-pass over an otherwise-opaque host document -
   Violet never parses the surrounding format. *)

type block =
  { src : string (* the Violet code between [open_] and [close] *)
  ; src_offset : int (* byte offset of [src] within the host document *)
  }

type segment =
  | Verbatim of string
  | Block of block

(* A range over [text]'s bytes [\[b, e)], tagged with [source] so diagnostics
   point into the host document. Walks [text] to recover line/column, so only
   call it off the hot path (i.e. when reporting an error). *)
let range_of ~source (text : string) (b : int) (e : int) : Asai.Range.t =
  let pos off : Lexing.position =
    let line = ref 1
    and bol = ref 0 in
    for k = 0 to off - 1 do
      if text.[k] = '\n'
      then begin
        incr line;
        bol := k + 1
      end
    done;
    { Lexing.pos_fname = source; pos_lnum = !line; pos_bol = !bol; pos_cnum = off }
  in
  Asai.Range.of_lex_range (pos b, pos e)
;;

let scan ~(delim : Delim.t) ~(source : string) (text : string) : segment list =
  let n = String.length text in
  let open_len = String.length delim.open_ in
  let close_len = String.length delim.close in
  let buf = Buffer.create 256 in
  let segs = Dynarray.create () in
  let flush_verbatim () =
    if Buffer.length buf > 0
    then begin
      Dynarray.add_last segs (Verbatim (Buffer.contents buf));
      Buffer.clear buf
    end
  in
  let starts_with marker marker_len p =
    p + marker_len <= n && String.equal (String.sub text p marker_len) marker
  in
  let find_close body_start =
    let open_off = body_start - open_len in
    let rec go j =
      if j + close_len > n
      then
        Violet_common.Reporter.fatalf
          ~loc:(range_of ~source text open_off j)
          Parse_error
          "unterminated %s block: missing closing `%s`"
          delim.open_
          delim.close
      else if starts_with delim.close close_len j
      then j
      else go (j + 1)
    in
    go body_start
  in
  let i = ref 0 in
  while !i < n do
    if starts_with delim.open_ open_len !i
    then begin
      flush_verbatim ();
      let body_start = !i + open_len in
      let close = find_close body_start in
      let src = String.sub text body_start (close - body_start) in
      Dynarray.add_last segs (Block { src; src_offset = body_start });
      i := close + close_len
    end
    else begin
      Buffer.add_char buf text.[!i];
      incr i
    end
  done;
  flush_verbatim ();
  Dynarray.to_list segs
;;

let%expect_test "scan splits prose and code blocks" =
  let show = function
    | Verbatim s -> Printf.printf "V(%s)" s
    | Block { src; src_offset } -> Printf.printf "B(%S,@%d)" src src_offset
  in
  List.iter show (scan ~delim:Delim.scrbl ~source:"doc.vt.scrbl" "a@vt|{x}|b@vt|{y}|c");
  [%expect {| V(a)B("x",@6)V(b)B("y",@15)V(c) |}]
;;

let%expect_test "scan keeps Violet braces and backslashes verbatim" =
  (match scan ~delim:Delim.scrbl ~source:"doc.vt.scrbl" "p@vt|{\\let f => {a}}|q" with
   | [ Verbatim a; Block { src; _ }; Verbatim b ] -> Printf.printf "%s | %s | %s" a src b
   | _ -> print_string "unexpected");
  [%expect {| p | \let f => {a} | q |}]
;;

let%expect_test "scan reports an unterminated block with a source location" =
  Violet_common.Reporter.run
    ~emit:(fun _ -> ())
    ~fatal:(fun d ->
      let loc = Option.get d.Asai.Diagnostic.explanation.loc in
      match Asai.Range.view loc with
      | `Range (s, _) ->
        Format.printf
          "%s:%d:%d: %t@."
          (match s.source with
           | `File f -> f
           | `String _ -> "?")
          s.line_num
          (s.offset - s.start_of_line)
          d.explanation.value
      | `End_of_file _ -> ())
    (fun () ->
       ignore
         (scan ~delim:Delim.scrbl ~source:"doc.vt.scrbl" "line one\n@vt|{ \\let f => a"));
  [%expect {| doc.vt.scrbl:2:0: unterminated @vt|{ block: missing closing `}|` |}]
;;

let%expect_test "scan honors an arbitrary caller-supplied delimiter" =
  let delim = Delim.{ open_ = "```violet"; close = "```" } in
  let show = function
    | Verbatim s -> Printf.printf "V(%s)" s
    | Block { src; src_offset } -> Printf.printf "B(%S,@%d)" src src_offset
  in
  List.iter
    show
    (scan ~delim ~source:"doc.md" "prose\n```violet\n\\let f => f\n```\nmore prose");
  [%expect
    {|
    V(prose
    )B("\n\\let f => f\n",@15)V(
    more prose)
    |}]
;;

let%expect_test "a multi-character close token spanning a newline is matched" =
  let delim = Delim.{ open_ = "<!--vt"; close = "vt-->" } in
  (match scan ~delim ~source:"doc.html" "x<!--vt\\let a => a\nvt-->y" with
   | [ Verbatim "x"; Block { src; _ }; Verbatim "y" ] -> print_string src
   | _ -> print_string "unexpected");
  [%expect
    {| \let a => a
 |}]
;;
