(* Scan a [*.vt.scrbl] document into verbatim prose and Violet code blocks.

   A code block is a scribble pipe-brace form, [@vt|{ ... }|]. The pipe-brace
   body keeps Violet syntax ([\], [{], [}], [=>], [|]) literal; the only sequence
   that ends a body is [}|], which generated/authored code must therefore avoid
   (the highlighter additionally escapes [|] in its output so it can never
   produce [}|]).

   This is a purely textual pre-pass - [@vt] is not a real racket binding
   because the weaver rewrites the block away before tr-notes runs. *)

type block =
  { src : string (* the Violet code between [|{] and [}|] *)
  ; src_offset : int (* byte offset of [src] within the scrbl document *)
  }

type segment =
  | Verbatim of string
  | Block of block

let vt_open = "@vt|{"

(* A range over [text]'s bytes [\[b, e)], tagged with [source] so diagnostics
   point into the scrbl document. Walks [text] to recover line/column, so only
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

let scan ~(source : string) (text : string) : segment list =
  let n = String.length text in
  let buf = Buffer.create 256 in
  let segs = ref [] in
  let flush_verbatim () =
    if Buffer.length buf > 0
    then begin
      segs := Verbatim (Buffer.contents buf) :: !segs;
      Buffer.clear buf
    end
  in
  let starts_with marker p =
    let lm = String.length marker in
    p + lm <= n && String.equal (String.sub text p lm) marker
  in
  let find_close body_start =
    let open_off = body_start - String.length vt_open in
    let rec go j =
      if j + 1 >= n
      then
        Violet_common.Reporter.fatalf
          ~loc:(range_of ~source text open_off j)
          Parse_error
          "unterminated @vt|{ block: missing closing `}|`"
      else if text.[j] = '}' && text.[j + 1] = '|'
      then j
      else go (j + 1)
    in
    go body_start
  in
  let i = ref 0 in
  while !i < n do
    if starts_with vt_open !i
    then begin
      flush_verbatim ();
      let body_start = !i + String.length vt_open in
      let close = find_close body_start in
      let src = String.sub text body_start (close - body_start) in
      segs := Block { src; src_offset = body_start } :: !segs;
      i := close + 2
    end
    else begin
      Buffer.add_char buf text.[!i];
      incr i
    end
  done;
  flush_verbatim ();
  List.rev !segs
;;

let%expect_test "scan splits prose and code blocks" =
  let show = function
    | Verbatim s -> Printf.printf "V(%s)" s
    | Block { src; src_offset } -> Printf.printf "B(%S,@%d)" src src_offset
  in
  List.iter show (scan ~source:"doc.scrbl" "a@vt|{x}|b@vt|{y}|c");
  [%expect {| V(a)B("x",@6)V(b)B("y",@15)V(c) |}]
;;

let%expect_test "scan keeps Violet braces and backslashes verbatim" =
  (match scan ~source:"doc.scrbl" "p@vt|{\\let f => {a}}|q" with
   | [ Verbatim a; Block { src; _ }; Verbatim b ] -> Printf.printf "%s | %s | %s" a src b
   | _ -> print_string "unexpected");
  [%expect {| p | \let f => {a} | q |}]
;;

let%expect_test "scan reports an unterminated @vt block with a source location" =
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
    (fun () -> ignore (scan ~source:"doc.scrbl" "line one\n@vt|{ \\let f => a"));
  [%expect {| doc.scrbl:2:0: unterminated @vt|{ block: missing closing `}|` |}]
;;
