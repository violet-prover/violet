type dep_source =
  | Path of string
  | Git of
      { url : string
      ; rev : string
      }
[@@deriving show]

type dep =
  { key : string
  ; source : dep_source
  }
[@@deriving show]

(* One file extension's literate configuration, for [violet weave] — a
   project can mix host document formats (`.md` fenced blocks alongside
   `.scrbl` pipe-brace blocks), each needing its own escape token pair *and*
   its own way of embedding rendered code back into that format. A plain
   string record here (rather than [Violet_literate.Delim.t]) keeps this
   library free of a dependency on [violet_literate], which itself depends on
   [violet_project].

   [open_]/[close]: the escape token pair [Block.scan] uses to find a Violet
   code block in that extension's documents.
   [output]: a shell command. Violet runs it once per code block, writing the
   block's rendered (highlighted) HTML fragment to its stdin; the command's
   stdout is spliced back into the document verbatim in place of the block.
   How to embed that fragment into the target format (wrap it, transform it,
   discard it) is entirely up to the command — Violet has no built-in notion
   of any particular output format.
   [css]: optional, project-root-relative path to write Violet's stylesheet
   to (hover tooltips etc.). Only meaningful for a rule whose [output] embeds
   the rendered HTML into an HTML-consuming target; omit it for anything else
   (e.g. a hook that reformats into Typst has no use for it) — Violet writes
   no stylesheet at all unless a rule asks for one. *)
type literate_rule =
  { ext : string (* file extension including the leading dot, e.g. ".md" *)
  ; open_ : string
  ; close : string
  ; output : string
  ; css : string option
  }
[@@deriving show]

type t =
  { name : string
  ; version : string
  ; deps : dep list
  ; literate : literate_rule list
  }
[@@deriving show]

open Manifest_lexer

type parser_state =
  { mutable cur : token
  ; lexbuf : Lexing.lexbuf
  }

let make_state s =
  let lexbuf = Lexing.from_string s in
  { cur = Manifest_lexer.token lexbuf; lexbuf }
;;

let advance st = st.cur <- Manifest_lexer.token st.lexbuf

let expect st t =
  if st.cur <> t
  then
    failwith
      (Printf.sprintf
         "parse: expected %s, got %s"
         (Manifest_lexer.show_token t)
         (Manifest_lexer.show_token st.cur));
  advance st
;;

let expect_string st =
  match st.cur with
  | STRING s ->
    advance st;
    s
  | t ->
    failwith
      (Printf.sprintf "parse: expected string, got %s" (Manifest_lexer.show_token t))
;;

let expect_ident st =
  match st.cur with
  | IDENT n ->
    advance st;
    n
  | t ->
    failwith
      (Printf.sprintf "parse: expected identifier, got %s" (Manifest_lexer.show_token t))
;;

(* attrs := '(' attr (',' attr)* ')' ; attr := ident '=' string *)
let parse_attrs st : (string * string) list =
  expect st LPAREN;
  let rec loop acc =
    let k = expect_ident st in
    expect st EQUALS;
    let v = expect_string st in
    let acc = (k, v) :: acc in
    match st.cur with
    | COMMA ->
      advance st;
      loop acc
    | RPAREN ->
      advance st;
      List.rev acc
    | t ->
      failwith
        (Printf.sprintf
           "parse_attrs: expected ',' or ')', got %s"
           (Manifest_lexer.show_token t))
  in
  loop []
;;

let literate_rule_of_attrs ~ext attrs : literate_rule =
  let lookup k = List.assoc_opt k attrs in
  match lookup "open", lookup "close", lookup "output" with
  | Some open_, Some close, Some output ->
    { ext; open_; close; output; css = lookup "css" }
  | None, _, _ -> failwith "literate: missing open"
  | _, None, _ -> failwith "literate: missing close"
  | _, _, None -> failwith "literate: missing output"
;;

let dep_source_of_attrs attrs : dep_source =
  let lookup k = List.assoc_opt k attrs in
  match lookup "path", lookup "git", lookup "rev" with
  | Some p, None, None -> Path p
  | None, Some url, Some rev -> Git { url; rev }
  | None, Some _, None -> failwith "dep: git requires rev"
  | Some _, Some _, _ -> failwith "dep: cannot have both path and git"
  | Some _, None, Some _ -> failwith "dep: path cannot have rev"
  | None, None, _ -> failwith "dep: must have path or git"
;;

let parse_string (s : string) : t =
  let st = make_state s in
  let name = ref None in
  let version = ref None in
  let deps = ref [] in
  let literate = ref [] in
  let rec loop () =
    match st.cur with
    | EOF -> ()
    | NAME ->
      advance st;
      let v = expect_string st in
      if !name <> None then failwith "duplicate \\name";
      name := Some v;
      loop ()
    | VERSION ->
      advance st;
      let v = expect_string st in
      if !version <> None then failwith "duplicate \\version";
      version := Some v;
      loop ()
    | DEP ->
      advance st;
      let key = expect_ident st in
      if List.exists (fun d -> d.key = key) !deps
      then failwith (Printf.sprintf "duplicate \\dep key: %s" key);
      let attrs = parse_attrs st in
      deps := { key; source = dep_source_of_attrs attrs } :: !deps;
      loop ()
    | LITERATE ->
      advance st;
      let ext = expect_string st in
      if List.exists (fun (r : literate_rule) -> r.ext = ext) !literate
      then failwith (Printf.sprintf "duplicate \\literate extension: %s" ext);
      let attrs = parse_attrs st in
      literate := literate_rule_of_attrs ~ext attrs :: !literate;
      loop ()
    | t ->
      failwith
        (Printf.sprintf "manifest: unexpected token %s" (Manifest_lexer.show_token t))
  in
  loop ();
  let name =
    match !name with
    | Some n -> n
    | None -> failwith "manifest: missing \\name"
  in
  let version =
    match !version with
    | Some v -> v
    | None -> failwith "manifest: missing \\version"
  in
  { name; version; deps = List.rev !deps; literate = List.rev !literate }
;;

let%expect_test "parse minimal manifest" =
  let m =
    parse_string
      {|
    \name "my-proj"
    \version "0.1.0"
  |}
  in
  Printf.printf "%s %s deps=%d" m.name m.version (List.length m.deps);
  [%expect {| my-proj 0.1.0 deps=0 |}]
;;

let%expect_test "parse manifest with deps" =
  let m =
    parse_string
      {|
    \name "my-proj"
    \version "0.1.0"
    \dep mylib  (path = "../mylib")
    \dep stdlib (git = "https://example/repo", rev = "main")
  |}
  in
  List.iter
    (fun d ->
       let src =
         match d.source with
         | Path p -> Printf.sprintf "path=%s" p
         | Git { url; rev } -> Printf.sprintf "git=%s@%s" url rev
       in
       Printf.printf "%s -> %s\n" d.key src)
    m.deps;
  [%expect
    {|
    mylib -> path=../mylib
    stdlib -> git=https://example/repo@main
    |}]
;;

let%expect_test "parse manifest with literate rules, keyed by extension" =
  let m =
    parse_string
      {|
    \name "my-proj"
    \version "0.1.0"
    \literate ".scrbl" (open = "@vt|{", close = "}|", output = "./weave-scrbl.sh", css = "assets/violet.css")
    \literate ".md" (open = "```violet", close = "```", output = "cat")
  |}
  in
  List.iter
    (fun (r : literate_rule) ->
       Printf.printf
         "%s: open=%S close=%S output=%S css=%s\n"
         r.ext
         r.open_
         r.close
         r.output
         (match r.css with
          | Some c -> Printf.sprintf "%S" c
          | None -> "none"))
    m.literate;
  [%expect
    {|
    .scrbl: open="@vt|{" close="}|" output="./weave-scrbl.sh" css="assets/violet.css"
    .md: open="```violet" close="```" output="cat" css=none
    |}]
;;

let%expect_test "manifest without literate rules leaves the list empty" =
  let m = parse_string {| \name "p" \version "1" |} in
  Printf.printf "%d" (List.length m.literate);
  [%expect {| 0 |}]
;;

let parse_err s =
  try
    let _ = parse_string s in
    "no error"
  with
  | Failure msg -> msg
;;

let%expect_test "parse error: missing name" =
  print_string (parse_err {| \version "1.0" |});
  [%expect {| manifest: missing \name |}]
;;

let%expect_test "parse error: duplicate dep key" =
  print_string
    (parse_err
       {|
    \name "p" \version "1"
    \dep foo (path = "a")
    \dep foo (path = "b")
  |});
  [%expect {| duplicate \dep key: foo |}]
;;

let%expect_test "parse error: duplicate literate extension" =
  print_string
    (parse_err
       {|
    \name "p" \version "1"
    \literate ".md" (open = "<!--vt", close = "vt-->", output = "cat")
    \literate ".md" (open = "@vt|{", close = "}|", output = "cat")
  |});
  [%expect {| duplicate \literate extension: .md |}]
;;

let%expect_test "parse error: literate missing close" =
  print_string
    (parse_err {| \name "p" \version "1" \literate ".md" (open = "x", output = "cat") |});
  [%expect {| literate: missing close |}]
;;

let%expect_test "parse error: literate missing output" =
  print_string
    (parse_err {| \name "p" \version "1" \literate ".md" (open = "x", close = "y") |});
  [%expect {| literate: missing output |}]
;;

let%expect_test "parse error: dep with both path and git" =
  print_string
    (parse_err
       {|
    \name "p" \version "1"
    \dep foo (path = "a", git = "https://b", rev = "c")
  |});
  [%expect {| dep: cannot have both path and git |}]
;;
