(* Integration tests for UTF-16 <-> byte position conversion at the LSP boundary.
   Kept in a top-level langserver module (rather than inside handlers/) so the
   ppx_expect corrected-file writer can resolve the source path under
   [(include_subdirs unqualified)].

   The last line of the source is "\let r : Nat => g \xce\xb2 \xce\xb1"
   (i.e. [\let r : Nat => g β α]). The Greek letters β (U+03B2) and α (U+03B1) are
   each 2 UTF-8 bytes but a single UTF-16 code unit, so on that line the [α] use
   sits at UTF-16 col 20 yet byte col 21 — a position the old byte=UTF-16 code
   would have mis-resolved to the neighboring [β] (which the index has at byte
   col 18..19). Incoming requests arrive in UTF-16 and must be converted to byte
   columns before index lookup; returned positions must be converted back to
   UTF-16. *)
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
