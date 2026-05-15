(* Fair benchmark. Compare old parser and Krishnaswami-style on a
   realistic mix of surface syntax.

   Both parsers run on the same input and build the same Surface.t AST
   (the show_top comparison below diffs every top). The generated input
   is split 50/50 between an LL(1) baseline and constructs that exercise
   the two hand-coded peek disambiguators in the typed parser
   (lib/violet/Parser.ml:1-10):

     - shapes 0-3: LL(1) baseline (lets, data, applications, arrows)
     - shape 4: `\let NAME (x : U) (y : U) : U => x`        -- header binders
     - shape 5: `\let NAME : (x : U) -> U -> U => \(z : U) -> z`
                                                            -- pi binder peek
                                                            -- + typed lambda peek
     - shape 6: `\let NAME {A : U} (x : A) : A => x`         -- implicit binder
     - shape 7: `\let NAME : U -> U => \x -> x`              -- untyped lambda *)
let () =
  Violet_elab.Reporter.run ~emit:(fun _ -> ()) ~fatal:(fun _ -> exit 1)
  @@ fun () ->
  let n_imports = 2_000 in
  let n_tops = 4_000 in
  let buf = Buffer.create (1 lsl 20) in
  for i = 1 to n_imports do
    Buffer.add_string buf (Printf.sprintf "\\import lib%d.utils\n" i)
  done;
  for i = 1 to n_tops do
    (* alternate between let/data shapes so spine, arrow, paren, ctor,
       binder, lambda, and implicit parsing all get exercised. *)
    match i mod 8 with
    | 0 ->
      Buffer.add_string
        buf
        (Printf.sprintf "\\let f%d : U -> U -> U => g%d (h%d x%d) y%d\n" i i i i i)
    | 1 ->
      Buffer.add_string
        buf
        (Printf.sprintf "\\let id%d : (U -> U) -> U -> U => f%d (g%d x%d)\n" i i i i)
    | 2 ->
      Buffer.add_string
        buf
        (Printf.sprintf
           "\\data T%d : U | mk%da : T%d | mk%db : T%d -> T%d -> T%d\n"
           i
           i
           i
           i
           i
           i
           i)
    | 3 ->
      Buffer.add_string
        buf
        (Printf.sprintf "\\let comp%d : U -> U -> U -> U => a%d b%d c%d\n" i i i i)
    | 4 ->
      Buffer.add_string buf (Printf.sprintf "\\let hdr%d (x : U) (y : U) : U => x\n" i)
    | 5 ->
      Buffer.add_string
        buf
        (Printf.sprintf "\\let pi%d : (x : U) -> U -> U => \\(z : U) -> z\n" i)
    | 6 ->
      Buffer.add_string buf (Printf.sprintf "\\let imp%d {A : U} (x : A) : A => x\n" i)
    | _ -> Buffer.add_string buf (Printf.sprintf "\\let unty%d : U -> U => \\x -> x\n" i)
  done;
  let src = Buffer.contents buf in
  let toks_list =
    let lexbuf = Lexing.from_string src in
    Violet_elab.Parser.tokens "<bench>" lexbuf
  in
  let toks_arr = Array.of_list toks_list in
  let typed_parser = Violet_elab.Parser.Grammar.p_module_named "<bench>" in
  let run_typed () = Violet_elab.Parser.P.parse typed_parser toks_arr 0 in
  let run_current () = OldParser.run toks_list (OldParser.p_all "<bench>") in
  (* sanity check: both parsers must produce the same AST. If the typed
     parser were skipping work (as the previous body_stub did), the
     show-comparison below would diverge. *)
  let _, typed_result = run_typed () in
  let current_result = run_current () in
  assert (List.length typed_result.imports = List.length current_result.imports);
  assert (List.length typed_result.tops = List.length current_result.tops);
  let show_top (t : Violet_elab.Surface.top Asai.Range.located) =
    Violet_elab.Surface.show_top t.value
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
  let old_min, old_med =
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
  Format.printf "benchmark: old parser min=%.4f s  median=%.4f s@." old_min old_med;
  Format.printf
    "benchmark: ratio (old_min / typed_min)       = %.2fx@."
    (old_min /. typed_min);
  Format.printf
    "benchmark: ratio (old_median / typed_median) = %.2fx@."
    (old_med /. typed_med)
;;
