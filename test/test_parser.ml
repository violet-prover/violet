(* Parser unit tests for typed-algebraic parser combinators.
   Tests correctness of specific parsing constructs. *)

let positive_test () =
  Violet_elab.Reporter.run ~emit:(fun _ -> ()) ~fatal:(fun _ -> exit 1)
  @@ fun () ->
  let parse_tops src =
    let lexbuf = Lexing.from_string src in
    let toks = Array.of_list (Violet_elab.Parser.tokens "<positive_test>" lexbuf) in
    let m = Violet_elab.Parser.parse_buf ~name:"<positive_test>" toks in
    m.Violet_elab.Surface.tops
  in
  (* Basic let binding parses OK *)
  let tops = parse_tops "\\let f : U -> U => \\x -> x\n" in
  match tops with
  | [ _ ] -> Format.printf "positive_test OK@."
  | _ ->
    Format.printf "positive_test FAIL@.";
    exit 1
;;

let goal_test () =
  Violet_elab.Reporter.run ~emit:(fun _ -> ()) ~fatal:(fun _ -> exit 1)
  @@ fun () ->
  let parse_tops src =
    let lexbuf = Lexing.from_string src in
    let toks = Array.of_list (Violet_elab.Parser.tokens "<goal_test>" lexbuf) in
    let m = Violet_elab.Parser.parse_buf ~name:"<goal_test>" toks in
    m.Violet_elab.Surface.tops
  in
  (* Elim-style where-clause parses OK *)
  let tops =
    parse_tops "\\let neg2 : U -> U \\where\n  neg2 b <= \\elim b\n  | neg2 x => x\n"
  in
  match tops with
  | [ _ ] -> Format.printf "goal_test OK@."
  | _ ->
    Format.printf "goal_test FAIL@.";
    exit 1
;;

let elim_intro_test () =
  Violet_elab.Reporter.run ~emit:(fun _ -> ()) ~fatal:(fun _ -> exit 1)
  @@ fun () ->
  let parse_tops src =
    let lexbuf = Lexing.from_string src in
    let toks = Array.of_list (Violet_elab.Parser.tokens "<elim_test>" lexbuf) in
    let m = Violet_elab.Parser.parse_buf ~name:"<elim_test>" toks in
    m.Violet_elab.Surface.tops
  in
  (* Bare intros — all explicit *)
  let tops1 =
    parse_tops "\\let f : (x : U) -> U \\where\n  f x <= \\elim x\n  | f x => x\n"
  in
  (match tops1 with
   | [ { Asai.Range.value =
           Violet_elab.Surface.Elim_def
             { intros = [ ("x", false) ]
             ; clauses = [ { patterns = [ Violet_elab.Surface.PVar "x" ]; _ } ]
             ; _
             }
       ; _
       }
     ] -> Format.printf "elim_intro_test OK  bare intros@."
   | _ ->
     Format.printf "elim_intro_test FAIL bare intros@.";
     exit 1);
  (* Bracketed intros — implicit + explicit *)
  let tops2 =
    parse_tops "\\let f : (x : U) -> U \\where\n  f {A} x <= \\elim x\n  | f x => x\n"
  in
  (match tops2 with
   | [ { Asai.Range.value =
           Violet_elab.Surface.Elim_def { intros = [ ("A", true); ("x", false) ]; _ }
       ; _
       }
     ] -> Format.printf "elim_intro_test OK  bracketed intros@."
   | _ ->
     Format.printf "elim_intro_test FAIL bracketed intros@.";
     exit 1);
  (* PImpVar in clause patterns *)
  let tops3 =
    parse_tops "\\let f : (x : U) -> U \\where\n  f x <= \\elim x\n  | f {A} x => x\n"
  in
  match tops3 with
  | [ { Asai.Range.value =
          Violet_elab.Surface.Elim_def
            { clauses =
                [ { patterns =
                      [ Violet_elab.Surface.PImpVar "A"; Violet_elab.Surface.PVar "x" ]
                  ; _
                  }
                ]
            ; _
            }
      ; _
      }
    ] -> Format.printf "elim_intro_test OK  PImpVar clause@."
  | _ ->
    Format.printf "elim_intro_test FAIL PImpVar clause@.";
    exit 1
;;

let record_top_test () =
  Violet_elab.Reporter.run ~emit:(fun _ -> ()) ~fatal:(fun _ -> exit 1)
  @@ fun () ->
  let parse_tops src =
    let lexbuf = Lexing.from_string src in
    let toks = Array.of_list (Violet_elab.Parser.tokens "<record_top_test>" lexbuf) in
    let m = Violet_elab.Parser.parse_buf ~name:"<record_top_test>" toks in
    m.Violet_elab.Surface.tops
  in
  (* Record with two fields, no parameters *)
  let tops = parse_tops "\\record Point : U\n  | x : Nat\n  | y : Nat" in
  (match tops with
   | [ { Asai.Range.value = Violet_elab.Surface.Record r; _ } ] ->
     if
       String.equal r.name "Point" && List.length r.fields = 2 && List.length r.params = 0
     then Format.printf "record_top_test OK  no-params@."
     else begin
       Format.printf
         "record_top_test FAIL no-params: name=%s fields=%d params=%d@."
         r.name
         (List.length r.fields)
         (List.length r.params);
       exit 1
     end
   | _ ->
     Format.printf "record_top_test FAIL no-params: wrong shape@.";
     exit 1);
  (* Record with two fields, two parameters *)
  let tops2 =
    parse_tops "\\record Sigma (A : U) (B : A -> U) : U\n  | fst : A\n  | snd : B fst"
  in
  match tops2 with
  | [ { Asai.Range.value = Violet_elab.Surface.Record r; _ } ] ->
    if String.equal r.name "Sigma" && List.length r.fields = 2 && List.length r.params = 2
    then Format.printf "record_top_test OK  with-params@."
    else begin
      Format.printf
        "record_top_test FAIL with-params: name=%s fields=%d params=%d@."
        r.name
        (List.length r.fields)
        (List.length r.params);
      exit 1
    end
  | _ ->
    Format.printf "record_top_test FAIL with-params: wrong shape@.";
    exit 1
;;

let record_lit_test () =
  Violet_elab.Reporter.run ~emit:(fun _ -> ()) ~fatal:(fun _ -> exit 1)
  @@ fun () ->
  let parse_tops src =
    let lexbuf = Lexing.from_string src in
    let toks = Array.of_list (Violet_elab.Parser.tokens "<record_lit_test>" lexbuf) in
    let m = Violet_elab.Parser.parse_buf ~name:"<record_lit_test>" toks in
    m.Violet_elab.Surface.tops
  in
  let rec peel = function
    | Violet_elab.Surface.Located { value; _ } -> peel value
    | t -> t
  in
  let peel_item = function
    | Violet_elab.Surface.SI_Atom a -> Violet_elab.Surface.SI_Atom (peel a)
    | other -> other
  in
  (* Helper: extract RecordLit from the Op_soup wrapper that the parser emits
     before operator resolution.  A bare `{ … }` at head position becomes
     Op_soup [ SI_Atom (RecordLit […]) ]. *)
  let unwrap_record_lit body =
    match peel body with
    | Violet_elab.Surface.Op_soup items ->
      (match List.map peel_item items with
       | [ Violet_elab.Surface.SI_Atom (Violet_elab.Surface.RecordLit entries) ] ->
         Some entries
       | _ -> None)
    | _ -> None
  in
  (* Empty record literal *)
  let tops0 = parse_tops "\\let p : Point => {}" in
  (match tops0 with
   | [ { Asai.Range.value = Violet_elab.Surface.Let (_, _, _, body); _ } ] ->
     (match unwrap_record_lit body with
      | Some [] -> Format.printf "record_lit_test OK  empty@."
      | _ ->
        Format.printf
          "record_lit_test FAIL empty: body=%s@."
          (Violet_elab.Surface.show_preterm body);
        exit 1)
   | _ ->
     Format.printf "record_lit_test FAIL empty: wrong shape@.";
     exit 1);
  (* Plain literal: { x = a, y = b } *)
  let tops1 = parse_tops "\\let p : Point => { x = a, y = b }" in
  (match tops1 with
   | [ { Asai.Range.value = Violet_elab.Surface.Let (_, _, _, body); _ } ] ->
     (match unwrap_record_lit body with
      | Some [ ("x", _); ("y", _) ] -> Format.printf "record_lit_test OK  plain-lit@."
      | _ ->
        Format.printf
          "record_lit_test FAIL plain-lit: body=%s@."
          (Violet_elab.Surface.show_preterm body);
        exit 1)
   | _ ->
     Format.printf "record_lit_test FAIL plain-lit: wrong shape@.";
     exit 1);
  (* Pun literal: { x, y } desugars to { x = x, y = y } *)
  let tops2 = parse_tops "\\let p : Point => { x, y }" in
  (match tops2 with
   | [ { Asai.Range.value = Violet_elab.Surface.Let (_, _, _, body); _ } ] ->
     (match unwrap_record_lit body with
      | Some [ ("x", xv); ("y", yv) ]
        when (match peel xv with
              | Violet_elab.Surface.Var [ "x" ] -> true
              | _ -> false)
             &&
             match peel yv with
             | Violet_elab.Surface.Var [ "y" ] -> true
             | _ -> false -> Format.printf "record_lit_test OK  pun-lit@."
      | _ ->
        Format.printf
          "record_lit_test FAIL pun-lit: body=%s@."
          (Violet_elab.Surface.show_preterm body);
        exit 1)
   | _ ->
     Format.printf "record_lit_test FAIL pun-lit: wrong shape@.";
     exit 1);
  (* Mixed: { x, y = e, z } desugars to { x = x, y = e, z = z } *)
  let tops3 = parse_tops "\\let p : Point => { x, y = e, z }" in
  (match tops3 with
   | [ { Asai.Range.value = Violet_elab.Surface.Let (_, _, _, body); _ } ] ->
     (match unwrap_record_lit body with
      | Some [ ("x", xv); ("y", _); ("z", zv) ]
        when (match peel xv with
              | Violet_elab.Surface.Var [ "x" ] -> true
              | _ -> false)
             &&
             match peel zv with
             | Violet_elab.Surface.Var [ "z" ] -> true
             | _ -> false -> Format.printf "record_lit_test OK  mixed-lit@."
      | _ ->
        Format.printf
          "record_lit_test FAIL mixed-lit: body=%s@."
          (Violet_elab.Surface.show_preterm body);
        exit 1)
   | _ ->
     Format.printf "record_lit_test FAIL mixed-lit: wrong shape@.";
     exit 1);
  (* Implicit-application f {x} must still parse (regression check).
     `f {x}` = Op_soup with head SI_Name "f" and tail SI_Imp_arg.
     The inner atom may be wrapped in Located, so we check structurally
     using the show_preterm output. *)
  let tops4 = parse_tops "\\let r : U => f {x}" in
  (match tops4 with
   | [ { Asai.Range.value = Violet_elab.Surface.Let (_, _, _, body); _ } ] ->
     (match peel body with
      | Violet_elab.Surface.Op_soup items ->
        let items = List.map peel_item items in
        (match items with
         | [ Violet_elab.Surface.SI_Name "f"; Violet_elab.Surface.SI_Imp_arg inner ] ->
           let inner_str = Violet_elab.Surface.show_preterm (peel inner) in
           if String.equal inner_str "x"
           then Format.printf "record_lit_test OK  implicit-app@."
           else begin
             Format.printf "record_lit_test FAIL implicit-app: inner=%s@." inner_str;
             exit 1
           end
         | _ ->
           Format.printf
             "record_lit_test FAIL implicit-app: body=%s@."
             (Violet_elab.Surface.show_preterm body);
           exit 1)
      | _ ->
        Format.printf
          "record_lit_test FAIL implicit-app: body=%s@."
          (Violet_elab.Surface.show_preterm body);
        exit 1)
   | _ ->
     Format.printf "record_lit_test FAIL implicit-app: wrong shape@.";
     exit 1);
  Format.printf "record_lit_test OK@."
;;

let record_update_test () =
  Violet_elab.Reporter.run ~emit:(fun _ -> ()) ~fatal:(fun _ -> exit 1)
  @@ fun () ->
  let parse_tops src =
    let lexbuf = Lexing.from_string src in
    let toks = Array.of_list (Violet_elab.Parser.tokens "<record_update_test>" lexbuf) in
    let m = Violet_elab.Parser.parse_buf ~name:"<record_update_test>" toks in
    m.Violet_elab.Surface.tops
  in
  let rec peel = function
    | Violet_elab.Surface.Located { value; _ } -> peel value
    | t -> t
  in
  let peel_item = function
    | Violet_elab.Surface.SI_Atom a -> Violet_elab.Surface.SI_Atom (peel a)
    | other -> other
  in
  (* Helper: unwrap RecordUpdate from Op_soup wrapper *)
  let unwrap_record_update body =
    match peel body with
    | Violet_elab.Surface.Op_soup items ->
      (match List.map peel_item items with
       | [ Violet_elab.Surface.SI_Atom (Violet_elab.Surface.RecordUpdate (base, entries))
         ] -> Some (base, entries)
       | _ -> None)
    | _ -> None
  in
  (* Simple single-field update: { p | x = z } *)
  let tops1 = parse_tops "\\let q : Point => { p | x = z }" in
  (match tops1 with
   | [ { Asai.Range.value = Violet_elab.Surface.Let (_, _, _, body); _ } ] ->
     (match unwrap_record_update body with
      | Some (_, [ ("x", _) ]) -> Format.printf "record_update_test OK  simple@."
      | _ ->
        Format.printf
          "record_update_test FAIL simple: body=%s@."
          (Violet_elab.Surface.show_preterm body);
        exit 1)
   | _ ->
     Format.printf "record_update_test FAIL simple: wrong shape@.";
     exit 1);
  (* Multi-field update: { p | x = z, y = w } *)
  let tops2 = parse_tops "\\let q : Point => { p | x = z, y = w }" in
  (match tops2 with
   | [ { Asai.Range.value = Violet_elab.Surface.Let (_, _, _, body); _ } ] ->
     (match unwrap_record_update body with
      | Some (_, [ ("x", _); ("y", _) ]) -> Format.printf "record_update_test OK  multi@."
      | _ ->
        Format.printf
          "record_update_test FAIL multi: body=%s@."
          (Violet_elab.Surface.show_preterm body);
        exit 1)
   | _ ->
     Format.printf "record_update_test FAIL multi: wrong shape@.";
     exit 1);
  (* Pun-style override: { p | x } desugars to { p | x = x } *)
  let tops3 = parse_tops "\\let q : Point => { p | x }" in
  (match tops3 with
   | [ { Asai.Range.value = Violet_elab.Surface.Let (_, _, _, body); _ } ] ->
     (match unwrap_record_update body with
      | Some (_, [ ("x", xv) ])
        when match peel xv with
             | Violet_elab.Surface.Var [ "x" ] -> true
             | _ -> false -> Format.printf "record_update_test OK  pun@."
      | _ ->
        Format.printf
          "record_update_test FAIL pun: body=%s@."
          (Violet_elab.Surface.show_preterm body);
        exit 1)
   | _ ->
     Format.printf "record_update_test FAIL pun: wrong shape@.";
     exit 1);
  (* Regression: plain literal { x = a } must still be RecordLit, not RecordUpdate *)
  let tops4 = parse_tops "\\let p : Point => { x = a }" in
  (match tops4 with
   | [ { Asai.Range.value = Violet_elab.Surface.Let (_, _, _, body); _ } ] ->
     (match peel body with
      | Violet_elab.Surface.Op_soup items ->
        (match List.map peel_item items with
         | [ Violet_elab.Surface.SI_Atom (Violet_elab.Surface.RecordLit _) ] ->
           Format.printf "record_update_test OK  regression-literal@."
         | _ ->
           Format.printf
             "record_update_test FAIL regression-literal: body=%s@."
             (Violet_elab.Surface.show_preterm body);
           exit 1)
      | _ ->
        Format.printf
          "record_update_test FAIL regression-literal: body=%s@."
          (Violet_elab.Surface.show_preterm body);
        exit 1)
   | _ ->
     Format.printf "record_update_test FAIL regression-literal: wrong shape@.";
     exit 1);
  (* Regression: implicit application f {x} must still work *)
  let tops5 = parse_tops "\\let r : U => f {x}" in
  (match tops5 with
   | [ { Asai.Range.value = Violet_elab.Surface.Let (_, _, _, body); _ } ] ->
     (match peel body with
      | Violet_elab.Surface.Op_soup items ->
        let items = List.map peel_item items in
        (match items with
         | [ Violet_elab.Surface.SI_Name "f"; Violet_elab.Surface.SI_Imp_arg _ ] ->
           Format.printf "record_update_test OK  regression-implicit-app@."
         | _ ->
           Format.printf
             "record_update_test FAIL regression-implicit-app: body=%s@."
             (Violet_elab.Surface.show_preterm body);
           exit 1)
      | _ ->
        Format.printf
          "record_update_test FAIL regression-implicit-app: body=%s@."
          (Violet_elab.Surface.show_preterm body);
        exit 1)
   | _ ->
     Format.printf "record_update_test FAIL regression-implicit-app: wrong shape@.";
     exit 1);
  Format.printf "record_update_test OK@."
;;

let projection_test () =
  Violet_elab.Reporter.run ~emit:(fun _ -> ()) ~fatal:(fun _ -> exit 1)
  @@ fun () ->
  let parse_tops src =
    let lexbuf = Lexing.from_string src in
    let toks = Array.of_list (Violet_elab.Parser.tokens "<projection_test>" lexbuf) in
    let m = Violet_elab.Parser.parse_buf ~name:"<projection_test>" toks in
    m.Violet_elab.Surface.tops
  in
  (* Simple projection *)
  let src1 = "\\let n : Nat => p.x" in
  let tops1 = parse_tops src1 in
  (match tops1 with
   | [ { Asai.Range.value = Violet_elab.Surface.Let (_, _, _, body); _ } ] ->
     Printf.printf "simple: %s\n" (Violet_elab.Surface.show_preterm body)
   | _ -> Printf.printf "simple: unexpected\n");
  (* Chained projection -- left-associative *)
  let src2 = "\\let n : Nat => r.x.y" in
  let tops2 = parse_tops src2 in
  (match tops2 with
   | [ { Asai.Range.value = Violet_elab.Surface.Let (_, _, _, body); _ } ] ->
     Printf.printf "chained: %s\n" (Violet_elab.Surface.show_preterm body)
   | _ -> Printf.printf "chained: unexpected\n");
  (* Projection on application -- (f x).y *)
  let src3 = "\\let n : Nat => (f x).y" in
  let tops3 = parse_tops src3 in
  (match tops3 with
   | [ { Asai.Range.value = Violet_elab.Surface.Let (_, _, _, body); _ } ] ->
     Printf.printf "appl: %s\n" (Violet_elab.Surface.show_preterm body)
   | _ -> Printf.printf "appl: unexpected\n");
  (* Regression: Nat/zero must parse as Var ["Nat"; "zero"], not affected by dot *)
  let src4 = "\\let n : Nat => Nat/zero" in
  let tops4 = parse_tops src4 in
  (match tops4 with
   | [ { Asai.Range.value = Violet_elab.Surface.Let (_, _, _, body); _ } ] ->
     Printf.printf "qname: %s\n" (Violet_elab.Surface.show_preterm body)
   | _ -> Printf.printf "qname: unexpected\n");
  print_endline "projection_test OK"
;;

let pattern_record_test () =
  Violet_elab.Reporter.run ~emit:(fun _ -> ()) ~fatal:(fun _ -> exit 1)
  @@ fun () ->
  let parse_tops src =
    let lexbuf = Lexing.from_string src in
    let toks = Array.of_list (Violet_elab.Parser.tokens "<pattern_record_test>" lexbuf) in
    let m = Violet_elab.Parser.parse_buf ~name:"<pattern_record_test>" toks in
    m.Violet_elab.Surface.tops
  in
  (* Use stack-move style `<= \intro; <= \split` which is the correct
     \split syntax in Violet.  The elim-style `name p <= \split` is not
     part of the grammar — \split is always a stack move. *)
  let src =
    "\\let swap : Pair Nat Nat -> Pair Nat Nat \\where\n\
    \  <= \\intro\n\
    \  <= \\split\n\
    \  | swap { fst = a, snd = b } => { fst = b, snd = a }"
  in
  let tops = parse_tops src in
  (match tops with
   | [ _ ] -> Format.printf "pattern_record_test OK@."
   | _ ->
     Format.printf "pattern_record_test FAIL: expected 1 top, got %d@." (List.length tops);
     exit 1);
  (* Verify the PRecord pattern is actually present in the clause.
     The \split via stack moves produces a Stack_def top. *)
  (match tops with
   | [ { Asai.Range.value =
           Violet_elab.Surface.Stack_def
             { clauses =
                 [ { patterns =
                       [ Violet_elab.Surface.PRecord
                           [ ("fst", Violet_elab.Surface.PVar "a")
                           ; ("snd", Violet_elab.Surface.PVar "b")
                           ]
                       ]
                   ; _
                   }
                 ]
             ; _
             }
       ; _
       }
     ] -> Format.printf "pattern_record_test OK  PRecord structure@."
   | _ ->
     Format.printf
       "pattern_record_test FAIL  unexpected structure (parse may still be OK)@.");
  Format.printf "pattern_record_test OK@."
;;

let unicode_ident_test () =
  let lex_all src =
    let lexbuf = Lexing.from_string src in
    let rec loop acc =
      match Violet_elab.Lexer.token lexbuf with
      | Violet_elab.Lexer.EOF -> List.rev acc
      | t -> loop (t :: acc)
    in
    loop []
  in
  let open Violet_elab.Lexer in
  let expect label src expected =
    let got = lex_all src in
    if got = expected
    then Format.printf "unicode_ident_test OK  %s@." label
    else (
      Format.printf "unicode_ident_test FAIL %s@." label;
      List.iter (fun t -> Format.printf "  got: %a@." pp_token t) got;
      exit 1)
  in
  (* 2-byte UTF-8 letters: Greek, Cyrillic. *)
  expect "lone α" "α" [ IDENT "α" ];
  expect "Greek run" "αβγ" [ IDENT "αβγ" ];
  expect "Cyrillic" "Привет" [ IDENT "Привет" ];
  (* 2-byte letter mixed with ASCII identifier chars. *)
  expect "α-1" "α-1" [ IDENT "α-1" ];
  expect "x_β" "x_β" [ IDENT "x_β" ];
  (* 3-byte symbols still lex as SYMBOL, and identifier boundaries hold
     when a letter is adjacent to a 3-byte operator. *)
  expect "α≤β" "α≤β" [ IDENT "α"; SYMBOL "≤"; IDENT "β" ];
  (* Reserved 3-byte token still wins via first-rule precedence. *)
  expect "lone ⊔" "⊔" [ JOIN ];
  (* Letter-like Symbols block (3-byte UTF-8, 0xE2 0x84/0x85): ℕ ℝ ℤ. *)
  expect "lone ℕ" "ℕ" [ IDENT "ℕ" ];
  expect "ℕ+ℝ" "ℕ+ℝ" [ IDENT "ℕ"; SYMBOL "+"; IDENT "ℝ" ];
  (* Math Alphanumeric block (4-byte UTF-8): 𝓤 standalone and adjacent
     to a 3-byte operator must not be absorbed into the SYMBOL run. *)
  expect "lone 𝓤" "𝓤" [ IDENT "𝓤" ];
  expect "𝓤≤𝓥" "𝓤≤𝓥" [ IDENT "𝓤"; SYMBOL "≤"; IDENT "𝓥" ];
  (* All four Mathematical Bold Script glyphs used as universe names. *)
  expect "𝓣 𝓤 𝓥 𝓦" "𝓣 𝓤 𝓥 𝓦" [ IDENT "𝓣"; IDENT "𝓤"; IDENT "𝓥"; IDENT "𝓦" ];
  (* Universe declaration with math-bold letter — mirrors example/src/operators.vt *)
  let toks =
    let lexbuf = Lexing.from_string "\\universe 𝓤\n" in
    let rec loop acc =
      match Violet_elab.Lexer.token lexbuf with
      | Violet_elab.Lexer.EOF -> List.rev acc
      | t -> loop (t :: acc)
    in
    loop []
  in
  match toks with
  | [ UNIVERSE; IDENT "𝓤" ] -> Format.printf "unicode_ident_test OK  \\universe 𝓤@."
  | _ ->
    Format.printf "unicode_ident_test FAIL \\universe 𝓤@.";
    exit 1
;;

let benchmark () = Format.printf "benchmark: skipped in unit-test mode@."

let () =
  positive_test ();
  goal_test ();
  elim_intro_test ();
  record_top_test ();
  record_lit_test ();
  record_update_test ();
  projection_test ();
  pattern_record_test ();
  unicode_ident_test ();
  benchmark ()
;;
