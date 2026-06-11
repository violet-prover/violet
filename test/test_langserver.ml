(* Integration tests for UTF-16 <-> byte position conversion at the LSP boundary,
   exercising the handlers end-to-end (Doc_store + Checker + Hover/Definition/
   References). Whitebox unit tests of the conversion itself live inline in
   [lib/langserver/encoding.ml].

   The last line of the source is "\let r : Nat => g \xce\xb2 \xce\xb1"
   (i.e. [\let r : Nat => g β α]). The Greek letters β (U+03B2) and α (U+03B1) are
   each 2 UTF-8 bytes but a single UTF-16 code unit, so on that line the [α] use
   sits at UTF-16 col 20 yet byte col 21 — a position the old byte=UTF-16 code
   would have mis-resolved to the neighboring [β] (which the index has at byte
   col 18..19). Incoming requests arrive in UTF-16 and must be converted to byte
   columns before index lookup; returned positions must be converted back to
   UTF-16. *)
open Violet_langserver

let utf16_test_source =
  String.concat
    "\n"
    [ {|\universe U|} (* L0 *)
    ; {|\data Nat : U|} (* L1 *)
    ; {|  | zero : Nat|} (* L2 *)
    ; "\\let \xce\xb1 : Nat => zero" (* L3: \let α : Nat => zero *)
    ; "\\let \xce\xb2 : Nat => zero" (* L4: \let β : Nat => zero *)
    ; {|\let g (a b : Nat) : Nat => a|} (* L5 *)
    ; "\\let r : Nat => g \xce\xb2 \xce\xb1" (* L6: \let r : Nat => g β α *)
    ; ""
    ]
;;

let contains ~affix s =
  let la = String.length affix
  and ls = String.length s in
  let rec go i = i + la <= ls && (String.sub s i la = affix || go (i + 1)) in
  la = 0 || go 0
;;

let setup source ~module_name =
  let store = Doc_store.create () in
  let project_index = Project_index.create () in
  let uri =
    Linol_lsp.Lsp.Types.DocumentUri.of_path (Printf.sprintf "/tmp/%s.vt" module_name)
  in
  let _ = Doc_store.update store ~uri ~text:source ~version:1 in
  let c = Checker.create ~store ~project_index in
  Checker.recheck c ~uri;
  store, project_index, c, uri
;;

let%expect_test "hover at a UTF-16 col after a multibyte glyph resolves the right token" =
  let store, _pi, _c, uri = setup utf16_test_source ~module_name:"Utf16Hover" in
  (* The [α] use is at UTF-16 col 20 (byte col 21) on LSP line 6. Treating it as
     a byte column would land on the [β] entry instead. *)
  let pos = Linol_lsp.Lsp.Types.Position.create ~line:6 ~character:20 in
  (match Hover.handle store ~uri ~position:pos with
   | None -> Printf.printf "no-hover"
   | Some h ->
     (match h.contents with
      | `MarkupContent mc ->
        Printf.printf
          "alpha=%b beta=%b"
          (contains ~affix:"\xce\xb1" mc.value)
          (contains ~affix:"\xce\xb2" mc.value)
      | _ -> Printf.printf "other"));
  [%expect
    {|
    +checking [module] Utf16Hover (/tmp/Utf16Hover.vt)
    alpha=true beta=false
    |}]
;;

let%expect_test "goto-definition resolves and returns a UTF-16 Position" =
  let store, pi, c, uri = setup utf16_test_source ~module_name:"Utf16Def" in
  (* Goto-def of the [α] use at LSP line 6 / UTF-16 col 20. Its declaration is on
     LSP line 3 where [α]'s name is at byte col 5 (no multibyte before it). *)
  let pos = Linol_lsp.Lsp.Types.Position.create ~line:6 ~character:20 in
  (match Definition.handle store pi c ~uri ~position:pos with
   | [] -> Printf.printf "no-def"
   | loc :: _ ->
     let s = loc.range.start in
     Printf.printf "line=%d character=%d" s.line s.character);
  [%expect
    {|
    +checking [module] Utf16Def (/tmp/Utf16Def.vt)
    line=3 character=5
    |}]
;;

let%expect_test "references return byte->UTF-16 converted positions" =
  let store, _pi, _c, uri = setup utf16_test_source ~module_name:"Utf16Refs" in
  (* Ask for references to [α] from its declaration (LSP line 3, col 5). The use
     on LSP line 6 must come back at UTF-16 col 20 (byte 21), proving the
     outgoing byte->UTF-16 conversion. *)
  let pos = Linol_lsp.Lsp.Types.Position.create ~line:3 ~character:5 in
  let refs = References.handle store ~uri ~position:pos in
  List.iter
    (fun (l : Linol_lsp.Lsp.Types.Location.t) ->
       Printf.printf
         "L%d:C%d-L%d:C%d\n"
         l.range.start.line
         l.range.start.character
         l.range.end_.line
         l.range.end_.character)
    refs;
  [%expect
    {|
    +checking [module] Utf16Refs (/tmp/Utf16Refs.vt)
    L6:C20-L6:C21
    L3:C0-L3:C20
    |}]
;;

(* Cross-file resolution. Two modules in the same directory:

   dep.vt:
     L0 \universe U
     L1 \export f
     L2 \let f (x : U) : U => x
     L3 \let α (y : U) : U => f y   -- α (1 UTF-16 unit, 2 bytes) before the f use

   On dep.vt L3 the [f] use sits at byte col 23 but UTF-16 col 22, so its
   converted column is observable only if conversion uses dep.vt's OWN text.

   main.vt (the open doc):
     L0 \universe U
     L1 \import dep
     L2 \let g (y : U) : U => f y   -- use of the imported f, byte/UTF-16 col 22

   The dep file is written to a real temp file because import resolution loads
   dep modules from disk (the loader's text_override only covers the open doc). *)

let dep_src =
  String.concat
    "\n"
    [ {|\universe U|} (* L0 *)
    ; {|\export f|} (* L1 *)
    ; {|\let f (x : U) : U => x|} (* L2 *)
    ; "\\let \xce\xb1 (y : U) : U => f y" (* L3: \let α (y : U) : U => f y *)
    ; ""
    ]
;;

let main_src =
  String.concat
    "\n"
    [ {|\universe U|} (* L0 *)
    ; {|\import dep|} (* L1 *)
    ; {|\let g (y : U) : U => f y|} (* L2 *)
    ; ""
    ]
;;

(* Build a directory under /tmp holding dep.vt (on disk) and an open main.vt
   doc that imports it, run a recheck, and return the store/checker/uris.

   A fixed /tmp subdir is used (rather than a randomized temp name) so the
   absolute paths the elaborator echoes in its "+checking [module] ..." trace
   are deterministic for the golden, matching the sibling tests' /tmp usage.
   The dep file is written to disk because import resolution loads dep modules
   from disk — the loader's text_override only covers the open doc. *)
let setup_cross_file () =
  let dir = "/tmp/violet_xfile" in
  (try Sys.remove (Filename.concat dir "dep.vt") with
   | Sys_error _ -> ());
  (try Sys.mkdir dir 0o700 with
   | Sys_error _ -> ());
  let dep_path = Filename.concat dir "dep.vt" in
  let main_path = Filename.concat dir "main.vt" in
  let oc = open_out_bin dep_path in
  output_string oc dep_src;
  close_out oc;
  let store = Doc_store.create () in
  let project_index = Project_index.create () in
  let main_uri = Linol_lsp.Lsp.Types.DocumentUri.of_path main_path in
  let _ = Doc_store.update store ~uri:main_uri ~text:main_src ~version:1 in
  let c = Checker.create ~store ~project_index in
  Checker.recheck c ~uri:main_uri;
  store, project_index, c, main_uri, dep_path, main_path
;;

let%expect_test "find-references resolves each location to its own file's uri and text" =
  let store, _pi, _c, main_uri, dep_path, main_path = setup_cross_file () in
  (* Query references from the [f] use in main.vt (LSP line 2, col 22). *)
  let pos = Linol_lsp.Lsp.Types.Position.create ~line:2 ~character:22 in
  let refs = References.handle store ~uri:main_uri ~position:pos in
  let in_dep =
    List.exists
      (fun (l : Linol_lsp.Lsp.Types.Location.t) ->
         Linol_lsp.Lsp.Types.DocumentUri.to_path l.uri = dep_path)
      refs
  in
  let in_main =
    List.exists
      (fun (l : Linol_lsp.Lsp.Types.Location.t) ->
         Linol_lsp.Lsp.Types.DocumentUri.to_path l.uri = main_path)
      refs
  in
  Printf.printf "in_dep=%b in_main=%b\n" in_dep in_main;
  (* The dep.vt [f] use on L3: byte col 23 converts to UTF-16 col 22 using
     dep.vt's text (the leading α is 2 bytes / 1 UTF-16 unit). *)
  List.iter
    (fun (l : Linol_lsp.Lsp.Types.Location.t) ->
       let path = Linol_lsp.Lsp.Types.DocumentUri.to_path l.uri in
       let which = if path = dep_path then "dep" else "main" in
       Printf.printf
         "%s L%d:C%d-L%d:C%d\n"
         which
         l.range.start.line
         l.range.start.character
         l.range.end_.line
         l.range.end_.character)
    refs;
  [%expect
    {|
    +checking [module] dep (/tmp/violet_xfile/dep.vt)
    +checking [module] main (/tmp/violet_xfile/main.vt)
    in_dep=true in_main=true
    dep L3:C22-L3:C23
    main L2:C22-L2:C23
    dep L2:C0-L2:C23
    dep L1:C8-L1:C9
    |}]
;;

let axiom_deps_source =
  String.concat
    "\n"
    [ {|\universe U|} (* L0 *)
    ; {|\axiom ua : U|} (* L1 *)
    ; {|\let foo : U => ua|} (* L2 *)
    ; ""
    ]
;;

let%expect_test "hover on a def that depends on an axiom shows depends-on line" =
  let store, _pi, _c, uri = setup axiom_deps_source ~module_name:"AxiomDeps" in
  (* [foo] is declared at LSP line 2, col 5 (\let foo ...). *)
  let pos = Linol_lsp.Lsp.Types.Position.create ~line:2 ~character:5 in
  (match Hover.handle store ~uri ~position:pos with
   | None -> Printf.printf "no-hover"
   | Some h ->
     (match h.contents with
      | `MarkupContent mc ->
        Printf.printf "has-dep-line=%b" (contains ~affix:"depends on axioms: ua" mc.value)
      | _ -> Printf.printf "other"));
  [%expect
    {|
    +checking [module] AxiomDeps (/tmp/AxiomDeps.vt)
    has-dep-line=true
    |}]
;;

let%expect_test "goto-definition across modules returns the target file's uri" =
  let store, pi, c, main_uri, dep_path, _main_path = setup_cross_file () in
  (* Goto-def of the [f] use in main.vt (LSP line 2, col 22). Its definition is
     dep.vt L2 where [f]'s name is at byte/UTF-16 col 5. *)
  let pos = Linol_lsp.Lsp.Types.Position.create ~line:2 ~character:22 in
  (match Definition.handle store pi c ~uri:main_uri ~position:pos with
   | [] -> Printf.printf "no-def"
   | loc :: _ ->
     let path = Linol_lsp.Lsp.Types.DocumentUri.to_path loc.uri in
     let which = if path = dep_path then "dep" else "other" in
     Printf.printf "file=%s L%d:C%d" which loc.range.start.line loc.range.start.character);
  [%expect
    {|
    +checking [module] dep (/tmp/violet_xfile/dep.vt)
    +checking [module] main (/tmp/violet_xfile/main.vt)
    +checking [module] dep (/tmp/violet_xfile/dep.vt)
    file=dep L2:C5
    |}]
;;
