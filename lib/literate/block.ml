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

let scan (text : string) : segment list =
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
    let rec go j =
      if j + 1 >= n
      then n (* unterminated: take the rest of the document *)
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
      i := if close >= n then n else close + 2
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
  List.iter show (scan "a@vt|{x}|b@vt|{y}|c");
  [%expect {| V(a)B("x",@6)V(b)B("y",@15)V(c) |}]
;;

let%expect_test "scan keeps Violet braces and backslashes verbatim" =
  (match scan "p@vt|{\\let f => {a}}|q" with
   | [ Verbatim a; Block { src; _ }; Verbatim b ] -> Printf.printf "%s | %s | %s" a src b
   | _ -> print_string "unexpected");
  [%expect {| p | \let f => {a} | q |}]
;;
