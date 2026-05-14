let positive_test () =
  Violet.Reporter.run ~emit:(fun _ -> ()) ~fatal:(fun _ -> exit 1)
  @@ fun () ->
  let examples = [ "term-only/bool"; "term-only/list" ] in
  List.iter
    (fun name ->
       let path = "../example/" ^ name ^ ".vt" in
       let typed_result = Violet.Parser.parse_file path in
       let legacy_result = OldParser.parse_file path in
       if List.length typed_result.imports <> List.length legacy_result.imports
       then begin
         Format.printf
           "positive_test FAIL %s: import count typed=%d legacy=%d@."
           path
           (List.length typed_result.imports)
           (List.length legacy_result.imports);
         exit 1
       end;
       if List.length typed_result.tops <> List.length legacy_result.tops
       then begin
         Format.printf
           "positive_test FAIL %s: top count typed=%d legacy=%d@."
           path
           (List.length typed_result.tops)
           (List.length legacy_result.tops);
         exit 1
       end;
       List.iter2
         (fun (a : Violet.Syntax.Surface.top Asai.Range.located)
           (b : Violet.Syntax.Surface.top Asai.Range.located) ->
            let sa = Violet.Syntax.Surface.show_top a.value in
            let sb = Violet.Syntax.Surface.show_top b.value in
            if sa <> sb
            then begin
              Format.printf
                "positive_test FAIL %s: top AST diverges@.  typed:  %s@.  legacy: %s@."
                path
                sa
                sb;
              exit 1
            end)
         typed_result.tops
         legacy_result.tops;
       Format.printf
         "positive_test OK  %s (%d imports, %d tops)@."
         path
         (List.length typed_result.imports)
         (List.length typed_result.tops))
    examples
;;

(* Fair benchmark.

   Both parsers run on the same LL(1)-subset input and build the same
   Surface.t AST. The input exercises:
     - imports
     - `let NAME : term := term` (no bindings)
     - `data NAME : term | ctor : term ...` (no params)
     - terms with applications, arrows, and parenthesised sub-terms

   We avoid `(x : T) -> body` style binders and typed lambdas, since the
   typed-algebraic framework is strictly LL(1) and cannot disambiguate
   them from `(t)`. Restricting to a common subset is what makes the
   comparison apples-to-apples — both parsers walk the same tokens and
   allocate the same AST shape. *)
let benchmark () =
  Violet.Reporter.run ~emit:(fun _ -> ()) ~fatal:(fun _ -> exit 1)
  @@ fun () ->
  let n_imports = 2_000 in
  let n_tops = 4_000 in
  let buf = Buffer.create (1 lsl 20) in
  for i = 1 to n_imports do
    Buffer.add_string buf (Printf.sprintf "import lib%d.utils\n" i)
  done;
  for i = 1 to n_tops do
    (* alternate between several let/data shapes so spine, arrow, paren,
       and ctor parsing all get exercised. *)
    match i mod 4 with
    | 0 ->
      Buffer.add_string
        buf
        (Printf.sprintf "let f%d : U -> U -> U := g%d (h%d x%d) y%d\n" i i i i i)
    | 1 ->
      Buffer.add_string
        buf
        (Printf.sprintf "let id%d : (U -> U) -> U -> U := f%d (g%d x%d)\n" i i i i)
    | 2 ->
      Buffer.add_string
        buf
        (Printf.sprintf
           "data T%d : U | mk%da : T%d | mk%db : T%d -> T%d -> T%d\n"
           i
           i
           i
           i
           i
           i
           i)
    | _ ->
      Buffer.add_string
        buf
        (Printf.sprintf "let comp%d : U -> U -> U -> U := a%d b%d c%d\n" i i i i)
  done;
  let src = Buffer.contents buf in
  let toks_list =
    let lexbuf = Lexing.from_string src in
    Violet.Parser.tokens "<bench>" lexbuf
  in
  let toks_arr = Array.of_list toks_list in
  let typed_parser = Violet.Parser.Grammar.p_module_named "<bench>" in
  let run_typed () = Violet.Parser.P.parse typed_parser toks_arr 0 in
  let run_current () = OldParser.run toks_list (OldParser.p_all "<bench>") in
  (* sanity check: both parsers must produce the same AST. If the typed
     parser were skipping work (as the previous body_stub did), the
     show-comparison below would diverge. *)
  let _, typed_result = run_typed () in
  let current_result = run_current () in
  assert (List.length typed_result.imports = List.length current_result.imports);
  assert (List.length typed_result.tops = List.length current_result.tops);
  let show_top (t : Violet.Syntax.Surface.top Asai.Range.located) =
    Violet.Syntax.Surface.show_top t.value
  in
  let typed_strs = List.map show_top typed_result.tops in
  let current_strs = List.map show_top current_result.tops in
  List.iter2
    (fun a b ->
       if a <> b
       then begin
         Format.printf "AST mismatch:@.  typed:   %s@.  current: %s@." a b;
         exit 1
       end)
    typed_strs
    current_strs;
  Format.printf
    "benchmark: AST equivalence verified for all %d tops@."
    (List.length typed_strs);
  let bench_one ~warmup ~iters f =
    for _ = 1 to warmup do
      let _ = f () in
      ()
    done;
    let samples = Array.make iters 0.0 in
    for i = 0 to iters - 1 do
      Gc.full_major ();
      let t0 = Sys.time () in
      let _ = f () in
      samples.(i) <- Sys.time () -. t0
    done;
    Array.sort compare samples;
    let mn = samples.(0) in
    let md = samples.(iters / 2) in
    mn, md
  in
  let n_warmup = 2 in
  let n_iters = 5 in
  let typed_min, typed_med =
    bench_one ~warmup:n_warmup ~iters:n_iters (fun () ->
      let _ = run_typed () in
      ())
  in
  let cur_min, cur_med =
    bench_one ~warmup:n_warmup ~iters:n_iters (fun () ->
      let _ = run_current () in
      ())
  in
  let tok_count = Array.length toks_arr in
  Format.printf
    "benchmark: %d imports + %d tops (%d tokens, %d iters + %d warmup)@."
    n_imports
    n_tops
    tok_count
    n_iters
    n_warmup;
  Format.printf
    "benchmark: typed parser   min=%.4f s  median=%.4f s@."
    typed_min
    typed_med;
  Format.printf "benchmark: old parser min=%.4f s  median=%.4f s@." cur_min cur_med;
  Format.printf
    "benchmark: ratio (typed_min / old_min)       = %.2fx@."
    (typed_min /. cur_min);
  Format.printf
    "benchmark: ratio (typed_median / old_median) = %.2fx@."
    (typed_med /. cur_med)
;;

let goal_test () =
  Violet.Reporter.run ~emit:(fun _ -> ()) ~fatal:(fun _ -> exit 1)
  @@ fun () ->
  let parse_tops src =
    let lexbuf = Lexing.from_string src in
    let toks = Array.of_list (Violet.Parser.tokens "<goal_test>" lexbuf) in
    let m = Violet.Parser.parse_buf ~name:"<goal_test>" toks in
    m.Violet.Syntax.Surface.tops
  in
  (* `?` alone as the body *)
  let tops1 = parse_tops "let f : U := ?" in
  (match tops1 with
   | [ { Asai.Range.value = Violet.Syntax.Surface.Let (_, _, _, body); _ } ] ->
     let s = Violet.Syntax.Surface.show_preterm body in
     if s = "?"
     then Format.printf "goal_test OK  bare ? -> %s@." s
     else begin
       Format.printf "goal_test FAIL bare ?: got %s@." s;
       exit 1
     end
   | _ ->
     Format.printf "goal_test FAIL bare ?: unexpected parse result@.";
     exit 1);
  (* `?here` as the body *)
  let tops2 = parse_tops "let f : U := ?here" in
  (match tops2 with
   | [ { Asai.Range.value = Violet.Syntax.Surface.Let (_, _, _, body); _ } ] ->
     let s = Violet.Syntax.Surface.show_preterm body in
     if s = "?here"
     then Format.printf "goal_test OK  ?here -> %s@." s
     else begin
       Format.printf "goal_test FAIL ?here: got %s@." s;
       exit 1
     end
   | _ ->
     Format.printf "goal_test FAIL ?here: unexpected parse result@.";
     exit 1)
;;

let () =
  positive_test ();
  goal_test ();
  benchmark ()
;;
