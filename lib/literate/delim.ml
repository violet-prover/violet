(* The pair of literal tokens that mark the start/end of a Violet code block
   inside an arbitrary host document. [block.ml] treats the host text as
   opaque and looks only for these two strings, so any document format that
   can offer a comment-safe token pair can carry literate Violet. *)

type t =
  { open_ : string
  ; close : string
  }

(* The scrbl pipe-brace form [weave] originally shipped as a hardcoded
   default. No longer applied automatically (every extension needs an
   explicit `\literate` rule in info.vt, no exceptions) — kept as a named
   constant so a project's own info.vt (or a test) can write this exact
   string instead of retyping it. *)
let scrbl = { open_ = "@vt|{"; close = "}|" }

(* [Filename.extension "foo.vt.md"] is [".md"] — matches how
   [Manifest.literate_rule.ext] is written in info.vt ([\literate ".md" (...)]). *)
let ext_of_path (path : string) : string = Filename.extension path

let rule_for ~(path : string) (rules : Violet_project.Manifest.literate_rule list)
  : Violet_project.Manifest.literate_rule
  =
  let ext = ext_of_path path in
  match
    List.find_opt
      (fun (r : Violet_project.Manifest.literate_rule) -> String.equal r.ext ext)
      rules
  with
  | Some r -> r
  | None ->
    Violet_common.Reporter.fatalf
      Parse_error
      "no `\\literate` rule configured for `%s` files: add `\\literate \"%s\" (open = \
       \"...\", close = \"...\", output = \"...\")` to info.vt"
      ext
      ext
;;

(* Resolve both the escape delimiter and the full matched [\literate] rule
   (carrying [output] and [css]) to weave [path] with. The matching project
   rule (§3 of the weave-output-hook design) is always required — it is the
   only source of [output]/[css], so there is no delimiter-only fallback (no
   more scrbl special case). [explicit] overrides only the delimiter for a
   one-off run; there is no CLI override for [output]/[css]. *)
let resolve
      ?(explicit : t option)
      ~(path : string)
      (rules : Violet_project.Manifest.literate_rule list)
  : t * Violet_project.Manifest.literate_rule
  =
  let rule = rule_for ~path rules in
  let delim =
    match explicit with
    | Some d -> d
    | None -> { open_ = rule.open_; close = rule.close }
  in
  delim, rule
;;
