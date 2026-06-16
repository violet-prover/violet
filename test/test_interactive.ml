open Violet_common

let parse_string ~filename src =
  let lexbuf = Lexing.from_string src in
  let toks = Array.of_list (Violet_surface.Parser.tokens filename lexbuf) in
  Violet_surface.Parser.parse_buf ~name:filename toks
;;

let with_handlers k =
  Reporter.run
    ~emit:(fun _ -> ())
    ~fatal:(fun d ->
      failwith
        (Format.asprintf "%s: %t" (Reporter.Message.show d.message) d.explanation.value))
  @@ fun () ->
  Violet_elab.Observer.run_silent
  @@ fun () ->
  Violet_elab.Context.S.run
    ~shadow:Violet_elab.Context.Handler.shadow
    ~not_found:Violet_elab.Context.Handler.not_found
    ~hook:Violet_elab.Context.Handler.hook
  @@ fun () ->
  Violet_elab.Env.S.run
    ~shadow:Violet_elab.Env.Handler.shadow
    ~not_found:Violet_elab.Env.Handler.not_found
    ~hook:Violet_elab.Env.Handler.hook
  @@ k
;;

let check_module_collecting ~filename src =
  let ast = parse_string ~filename src in
  let collector = Violet_interactive.Collector.create () in
  with_handlers (fun () ->
    Violet_elab.Elab.check_module
      ~on_event:(Violet_interactive.Collector.on_event collector)
      ast);
  Violet_interactive.Collector.to_index collector
;;

let id_src =
  {|\universe U
\let id (A : U) (x : A) : A => x
|}
;;

let pp_path p = String.concat "/" p

let fail msg =
  Format.printf "%s FAIL@." msg;
  exit 1
;;

let test_observer_emits_events () =
  let filename = "test_observer.vt" in
  let idx = check_module_collecting ~filename id_src in
  let entries = Violet_interactive.Index.all_entries idx in
  let defs =
    List.filter (fun (e : Violet_interactive.Index.entry) -> e.kind = Def) entries
  in
  let uses =
    List.filter (fun (e : Violet_interactive.Index.entry) -> e.kind = Use) entries
  in
  if List.length defs >= 1
  then Format.printf "observer_events OK  has defs (%d)@." (List.length defs)
  else begin
    Format.printf "observer_events FAIL  no defs@.";
    exit 1
  end;
  if List.length uses >= 1
  then Format.printf "observer_events OK  has uses (%d)@." (List.length uses)
  else begin
    Format.printf "observer_events FAIL  no uses@.";
    exit 1
  end;
  let def_names = List.map (fun (e : Violet_interactive.Index.entry) -> e.path) defs in
  if List.mem [ "id" ] def_names
  then Format.printf "observer_events OK  def named 'id'@."
  else begin
    Format.printf
      "observer_events FAIL  no def named 'id', got: [%s]@."
      (String.concat "; " (List.map pp_path def_names));
    exit 1
  end
;;

let test_find_at () =
  let filename = "test_find_at.vt" in
  let idx = check_module_collecting ~filename id_src in
  let entries = Violet_interactive.Index.all_entries idx in
  if List.length entries > 0
  then Format.printf "find_at OK  index has %d entries@." (List.length entries)
  else begin
    Format.printf "find_at FAIL  index is empty@.";
    exit 1
  end;
  (* The `x` variable use is at line 2, col 31-32 *)
  let result = Violet_interactive.Index.find_at ~source:filename ~line:2 ~col:31 idx in
  match result with
  | Some e ->
    Format.printf "find_at OK  found '%s' at (2,31)@." (pp_path e.path);
    if e.path = [ "x" ]
    then Format.printf "find_at OK  matched 'x'@."
    else begin
      Format.printf "find_at FAIL  expected 'x', got '%s'@." (pp_path e.path);
      exit 1
    end
  | None ->
    Format.printf "find_at FAIL  nothing found at (2,31)@.";
    exit 1
;;

(* Run a list of (module_path, filename, source) through ONE shared
   Context/Env scope and ONE collector, so cross-module imports resolve and
   every module's events land in a single index. Mirrors checker.ml's recheck
   loop (modules elaborated in dependency order under shared state). *)
let check_modules_collecting (mods : (string list * string * string) list) =
  let collector = Violet_interactive.Collector.create () in
  with_handlers (fun () ->
    List.iter
      (fun (module_path, filename, src) ->
         let ast = parse_string ~filename src in
         Violet_elab.Elab.check_module
           ~on_event:(Violet_interactive.Collector.on_event collector)
           ~module_path
           ast)
      mods);
  Violet_interactive.Collector.to_index collector
;;

(* The (start_line, start_col) of a range, line 1-based and col 0-based. *)
let start_pos (r : Asai.Range.t) : int * int =
  match Asai.Range.view r with
  | `Range (s, _) -> s.line_num, s.offset - s.start_of_line
  | `End_of_file p -> p.line_num, p.offset - p.start_of_line
;;

(* Assert goto-definition at (line, col) lands at a definition whose start is
   (exp_line, exp_col). line 1-based, col 0-based. *)
let assert_goto ~idx ~source ~label ~line ~col ~exp_line ~exp_col () =
  match Violet_interactive.Query.goto_definition ~source ~line ~col idx with
  | None -> fail (Printf.sprintf "%s: goto at (%d,%d) found nothing" label line col)
  | Some { loc; _ } ->
    let gl, gc = start_pos loc in
    if gl = exp_line && gc = exp_col
    then Format.printf "%s OK@." label
    else
      fail
        (Printf.sprintf
           "%s: goto at (%d,%d) landed at (%d,%d), expected (%d,%d)"
           label
           line
           col
           gl
           gc
           exp_line
           exp_col)
;;

(* Find the unique entry matching (kind, path, start line/col of its OWN loc)
   and assert its def_target start is (exp_line, exp_col). Used for the
   record-pun offset-collision regression, where two entries share one offset
   and find_at can only surface one. *)
let assert_entry_target
      ~idx
      ~label
      ~(kind : Violet_interactive.Index.entry_kind)
      ~path
      ~at_line
      ~at_col
      ~exp_line
      ~exp_col
      ()
  =
  let es = Violet_interactive.Index.all_entries idx in
  let matches =
    List.filter
      (fun (e : Violet_interactive.Index.entry) ->
         e.kind = kind
         && e.path = path
         &&
         let l, c = start_pos e.loc in
         l = at_line && c = at_col)
      es
  in
  match matches with
  | [ (e : Violet_interactive.Index.entry) ] ->
    (match e.def_target with
     | None -> fail (Printf.sprintf "%s: entry has no def_target" label)
     | Some t ->
       let tl, tc = start_pos t in
       if tl = exp_line && tc = exp_col
       then Format.printf "%s OK@." label
       else
         fail
           (Printf.sprintf
              "%s: def_target (%d,%d), expected (%d,%d)"
              label
              tl
              tc
              exp_line
              exp_col))
  | [] ->
    fail
      (Printf.sprintf "%s: no entry [%s] at (%d,%d)" label (pp_path path) at_line at_col)
  | _ ->
    fail
      (Printf.sprintf
         "%s: expected exactly one entry [%s] at (%d,%d), got %d"
         label
         (pp_path path)
         at_line
         at_col
         (List.length matches))
;;

let goto_src =
  {|\universe U
\data Nat : U
  | zero : Nat
  | suc : Nat -> Nat
\record P : U
  | fst : Nat
  | snd : Nat
\let id (A : U) (x : A) : A => x
\let lam : Nat -> Nat => \y -> y
\let sh (n : Nat) : Nat -> Nat => \n -> n
\let mk (a : Nat) : P => { fst => a | snd => zero }
\let f : Nat -> Nat \where
  f n <= \elim n
  | f zero => zero
  | f (suc m) => m
|}
;;

let test_goto_definition () =
  let filename = "test_goto_def.vt" in
  let idx = check_module_collecting ~filename goto_src in
  let g ~label ~line ~col ~exp_line ~exp_col =
    assert_goto ~idx ~source:filename ~label ~line ~col ~exp_line ~exp_col ()
  in
  (* myconst def still discoverable (smoke). *)
  let defs =
    List.filter
      (fun (e : Violet_interactive.Index.entry) -> e.kind = Def)
      (Violet_interactive.Index.all_entries idx)
  in
  if List.exists (fun (e : Violet_interactive.Index.entry) -> e.path = [ "id" ]) defs
  then Format.printf "goto_definition OK  'id' def exists@."
  else fail "goto_definition: no 'id' def";
  (* let-param use: `=> x` (line 8) jumps to the param `x` in `(x : A)`. The
     param `x` sits at col 17. *)
  g ~label:"goto let-param" ~line:8 ~col:31 ~exp_line:8 ~exp_col:17;
  (* lambda binder: body `y` jumps to `\y` binder (line 9, col 26). *)
  g ~label:"goto lambda-binder" ~line:9 ~col:31 ~exp_line:9 ~exp_col:26;
  (* SHADOWING: `\let sh (n : Nat) ... => \n -> n`. The body `n` must jump to
     the LAMBDA's `n` (col 35), NOT the param `n` (col 9). *)
  g ~label:"goto shadowing-nearest-binder" ~line:10 ~col:40 ~exp_line:10 ~exp_col:35;
  (* pattern var: `| f (suc m) => m` body `m` jumps to the pattern `m`
     (line 15, col 11), not the synthesized lambda's clause loc. *)
  g ~label:"goto pattern-var" ~line:15 ~col:17 ~exp_line:15 ~exp_col:11;
  (* record field use in literal `{ fst = a, ... }` jumps to the field decl
     `| fst : Nat` (line 6, col 4). *)
  g ~label:"goto record-field-use" ~line:11 ~col:27 ~exp_line:6 ~exp_col:4;
  (* pattern ctor `suc` jumps to the ctor decl (line 4, col 4). *)
  g ~label:"goto pattern-ctor" ~line:15 ~col:7 ~exp_line:4 ~exp_col:4
;;

(* Record-pun offset collision: in `{ fst }` the field-name Use and the
   value Var Use share one start offset. The per-entry def_target keeps them
   distinct — the field Use targets the field decl, the var Use targets the
   local/global `fst`. *)
let test_goto_record_pun_collision () =
  let filename = "test_pun.vt" in
  let src =
    {|\universe U
\data Nat : U
  | zero : Nat
\record P : U
  | fst : Nat
  | snd : Nat
\let fst : Nat => zero
\let mk (snd : Nat) : P => { fst | snd }
|}
  in
  let idx = check_module_collecting ~filename src in
  (* The pun `fst` (line 8) starts at col 29. The field Use [P;fst] there
     targets the field decl (line 5, col 4). *)
  assert_entry_target
    ~idx
    ~label:"pun field-use targets field decl"
    ~kind:Use
    ~path:[ "P"; "fst" ]
    ~at_line:8
    ~at_col:29
    ~exp_line:5
    ~exp_col:4
    ();
  (* The plain `fst` Var Use at the SAME offset targets the global `\let fst`
     (line 7, col 5) — proving the two same-offset entries don't collide. *)
  assert_entry_target
    ~idx
    ~label:"pun var-use targets its own def"
    ~kind:Use
    ~path:[ "fst" ]
    ~at_line:8
    ~at_col:29
    ~exp_line:7
    ~exp_col:5
    ()
;;

(* Cross-module same-name: two modules each define and use `f`. A use of `f`
   in module A must resolve to A's `f`, not B's (same-file preference in the
   bare-path fallback). *)
let test_goto_cross_module () =
  let a_file = "mod_a.vt" in
  let b_file = "mod_b.vt" in
  let a_src =
    {|\universe U
\export f
\let f (x : U) : U => x
\let usea (y : U) : U => f y
|}
  in
  let b_src =
    {|\universe U
\import a
\let f (x : U) : U => x
\let useb (y : U) : U => f y
|}
  in
  let idx = check_modules_collecting [ [ "a" ], a_file, a_src; [ "b" ], b_file, b_src ] in
  (* `f` in module A's `usea` body (line 4, col 25) resolves to A's `f`
     (line 3, col 5) in mod_a.vt — NOT B's. *)
  assert_goto
    ~idx
    ~source:a_file
    ~label:"cross-module use-in-A targets A"
    ~line:4
    ~col:25
    ~exp_line:3
    ~exp_col:5
    ();
  (* And the target must live in mod_a.vt, confirming same-file disambiguation. *)
  (match Violet_interactive.Query.goto_definition ~source:a_file ~line:4 ~col:25 idx with
   | Some { loc; _ } ->
     (match Violet_interactive.Index.source_of_range loc with
      | Some f when f = a_file -> Format.printf "cross-module target-file is mod_a OK@."
      | Some f ->
        fail (Printf.sprintf "cross-module: target file %s, expected %s" f a_file)
      | None -> fail "cross-module: target has no file")
   | None -> fail "cross-module: goto found nothing");
  (* Symmetric: `f` in module B's `useb` (line 4, col 25) resolves to B's own
     file — so the fallback is genuinely same-file directed, not first-wins. *)
  match Violet_interactive.Query.goto_definition ~source:b_file ~line:4 ~col:25 idx with
  | Some { loc; _ } ->
    (match Violet_interactive.Index.source_of_range loc with
     | Some f when f = b_file -> Format.printf "cross-module target-file is mod_b OK@."
     | Some f ->
       fail (Printf.sprintf "cross-module B: target file %s, expected %s" f b_file)
     | None -> fail "cross-module B: target has no file")
  | None -> fail "cross-module B: goto found nothing"
;;

let test_find_references () =
  let filename = "test_refs.vt" in
  let idx = check_module_collecting ~filename id_src in
  (* 'A' appears as binder and as return type annotation *)
  let a_entries = Violet_interactive.Index.entries_at_path [ "A" ] idx in
  if List.length a_entries >= 2
  then Format.printf "find_references OK  'A' has %d entries@." (List.length a_entries)
  else begin
    Format.printf
      "find_references FAIL  'A' has only %d entries@."
      (List.length a_entries);
    exit 1
  end
;;

let test_goal_events () =
  let src =
    {|\universe U
\let f : U => ?mygoal
|}
  in
  let filename = "test_goals.vt" in
  let idx = check_module_collecting ~filename src in
  let goals =
    List.filter
      (fun (e : Violet_interactive.Index.entry) -> e.kind = Goal)
      (Violet_interactive.Index.all_entries idx)
  in
  if List.length goals >= 1
  then begin
    let g = List.hd goals in
    Format.printf "goal_events OK  goal '%s'@." (pp_path g.path)
  end
  else begin
    Format.printf "goal_events FAIL  no goals found@.";
    exit 1
  end
;;

let test_collector_roundtrip () =
  let collector = Violet_interactive.Collector.create () in
  let idx = Violet_interactive.Collector.to_index collector in
  let entries = Violet_interactive.Index.all_entries idx in
  if entries = []
  then Format.printf "collector_roundtrip OK  empty@."
  else begin
    Format.printf "collector_roundtrip FAIL  expected empty@.";
    exit 1
  end
;;

(* One module exercising record fields (decl/literal/projection), lambda /
   let-param binders, and pattern ctor names + pattern variables. *)
let hover_src =
  {|\universe U
\data Nat : U
  | zero : Nat
  | suc : Nat -> Nat
\record P : U
  | fst : Nat
  | snd : Nat
\let mk (a : Nat) : P => { fst => a | snd => zero }
\let getf (p : P) : Nat => p.fst
\let lam : Nat -> Nat => \x -> x
\let f : Nat -> Nat \where
  f n <= \elim n
  | f zero => zero
  | f (suc m) => m
\data Box : U
  | pack : {n : Nat} -> Nat -> Box
\let g : Box -> Nat \where
  g b <= \elim b
  | g (pack {k} v) => v
|}
;;

(* Assert find_at at (line, col) yields an entry with the expected kind, path
   and (optionally) pp_ty. line is 1-based, col 0-based — same convention the
   existing find_at test uses. *)
let assert_at ~idx ~source ~label ~line ~col ~kind ?pp_ty ~path () =
  match Violet_interactive.Index.find_at ~source ~line ~col idx with
  | None -> fail (Printf.sprintf "%s: nothing found at (%d,%d)" label line col)
  | Some (e : Violet_interactive.Index.entry) ->
    if e.kind <> kind
    then
      fail
        (Printf.sprintf
           "%s: expected kind=%s got kind=%s path=%s"
           label
           (match kind with
            | Def -> "Def"
            | Use -> "Use"
            | Goal -> "Goal"
            | Binder -> "Binder")
           (match e.kind with
            | Def -> "Def"
            | Use -> "Use"
            | Goal -> "Goal"
            | Binder -> "Binder")
           (pp_path e.path));
    if e.path <> path
    then
      fail
        (Printf.sprintf
           "%s: expected path [%s], got [%s]"
           label
           (pp_path path)
           (pp_path e.path));
    (match pp_ty with
     | None -> ()
     | Some expected ->
       (match e.pp_ty with
        | Some got when String.equal got expected -> ()
        | Some got ->
          fail (Printf.sprintf "%s: expected pp_ty %s, got %s" label expected got)
        | None -> fail (Printf.sprintf "%s: expected pp_ty %s, got none" label expected)));
    Format.printf "%s OK@." label
;;

let test_hover_events () =
  let filename = "test_hover.vt" in
  let idx = check_module_collecting ~filename hover_src in
  let open Violet_interactive.Index in
  (* field-use in record literal `{ fst = a, ... }` (line 8, col 27) *)
  assert_at
    ~idx
    ~source:filename
    ~label:"hover field-literal-use"
    ~line:8
    ~col:27
    ~kind:Use
    ~pp_ty:"Nat"
    ~path:[ "P"; "fst" ]
    ();
  (* projection `p.fst` (line 9, col 29) *)
  assert_at
    ~idx
    ~source:filename
    ~label:"hover projection-use"
    ~line:9
    ~col:29
    ~kind:Use
    ~path:[ "P"; "fst" ]
    ();
  (* field decl in `\record P | fst : Nat` (line 6, col 4) *)
  assert_at
    ~idx
    ~source:filename
    ~label:"hover field-decl-def"
    ~line:6
    ~col:4
    ~kind:Def
    ~pp_ty:"Nat"
    ~path:[ "P"; "fst" ]
    ();
  (* lambda binder `x` in `\x -> x` (line 10, col 26) *)
  assert_at
    ~idx
    ~source:filename
    ~label:"hover lambda-binder"
    ~line:10
    ~col:26
    ~kind:Binder
    ~pp_ty:"Nat"
    ~path:[ "x" ]
    ();
  (* let-param binder `a` in `(a : Nat)` (line 8, col 9) *)
  assert_at
    ~idx
    ~source:filename
    ~label:"hover let-param-binder"
    ~line:8
    ~col:9
    ~kind:Binder
    ~pp_ty:"Nat"
    ~path:[ "a" ]
    ();
  (* pattern ctor `suc` in `| f (suc m)` (line 14, col 7) *)
  assert_at
    ~idx
    ~source:filename
    ~label:"hover pattern-ctor-use"
    ~line:14
    ~col:7
    ~kind:Use
    ~path:[ "Nat"; "suc" ]
    ();
  (* pattern variable `m` in `| f (suc m)` (line 14, col 11) *)
  assert_at
    ~idx
    ~source:filename
    ~label:"hover pattern-var-binder"
    ~line:14
    ~col:11
    ~kind:Binder
    ~pp_ty:"Nat"
    ~path:[ "m" ]
    ();
  (* ctor `pack` use in `| g (pack {k} v)` (line 19, col 7) *)
  assert_at
    ~idx
    ~source:filename
    ~label:"hover implicit-ctor-use"
    ~line:19
    ~col:7
    ~kind:Use
    ~path:[ "Box"; "pack" ]
    ();
  (* implicit pattern variable `k` in `{k}` (line 19, col 13) *)
  assert_at
    ~idx
    ~source:filename
    ~label:"hover implicit-pattern-var-binder"
    ~line:19
    ~col:13
    ~kind:Binder
    ~pp_ty:"Nat"
    ~path:[ "k" ]
    ();
  (* explicit pattern variable `v` (line 19, col 16) *)
  assert_at
    ~idx
    ~source:filename
    ~label:"hover explicit-pattern-var-after-implicit"
    ~line:19
    ~col:16
    ~kind:Binder
    ~pp_ty:"Nat"
    ~path:[ "v" ]
    ()
;;

(* The find_at tie-break: on equal span width, a non-Binder entry beats a
   Binder entry. Construct two same-width entries by hand and check of_events
   ranks the Use over the Binder. *)
let test_find_at_tiebreak () =
  let filename = "test_tiebreak.vt" in
  let mk_range ~s ~e : Asai.Range.t =
    let src = `File filename in
    let p offset : Asai.Range.position =
      { source = src; offset; start_of_line = 0; line_num = 1 }
    in
    Asai.Range.make (p s, p e)
  in
  let loc = mk_range ~s:0 ~e:2 in
  let ty = Violet_kernel.Syntax.Core.Universe Violet_kernel.Level.LZero in
  let events =
    [ Violet_elab.Observer.Binder { path = [ "b" ]; loc; ty = Some ty; pp_ty = Some "U" }
    ; Violet_elab.Observer.Use { path = [ "u" ]; loc; def_loc = None; ty; pp_ty = "U" }
    ]
  in
  let idx = Violet_interactive.Index.of_events events in
  match Violet_interactive.Index.find_at ~source:filename ~line:1 ~col:0 idx with
  | Some { kind = Use; path = [ "u" ]; _ } ->
    Format.printf "find_at_tiebreak OK  Use beats Binder on equal width@."
  | Some e ->
    Format.printf "find_at_tiebreak FAIL  got path %s@." (pp_path e.path);
    exit 1
  | None ->
    Format.printf "find_at_tiebreak FAIL  nothing found@.";
    exit 1
;;

(* Regression source for the elim-header hover bugs. Shaped like a real
   `\let ... \where ... <= \elim` definition with two intros and zero/suc
   clauses. Line/col references below are 1-based line, 0-based col.
     line 1: \let add : (m n : Nat) -> Nat \where
     line 2:   add m n <= \elim m
     line 3:   | add zero n => n
     line 4:   | add (suc k) n => suc (add k n)  *)
let elim_header_src =
  {|\universe U
\data Nat : U
  | zero : Nat
  | suc : Nat -> Nat
\let add : (m n : Nat) -> Nat \where
  add m n <= \elim m
  | add zero n => n
  | add (suc k) n => suc k
|}
;;

let test_elim_header_hover () =
  let filename = "test_elim_header.vt" in
  let idx = check_module_collecting ~filename elim_header_src in
  let open Violet_interactive.Index in
  (* Bug 1: hover on the def name `add` in `\let add` (line 5, col 0) must be
     the definition, NOT a Binder named `m` synthesized from the intro
     lambdas. *)
  assert_at
    ~idx
    ~source:filename
    ~label:"elim-header def-name not binder"
    ~line:5
    ~col:0
    ~kind:Def
    ~path:[ "add" ]
    ();
  (* Bug 2: hover on the intro `m` on the header line `add m n <= \elim m`
     (line 6, col 6) is a Binder of type Nat — not the whole signature. *)
  assert_at
    ~idx
    ~source:filename
    ~label:"elim-header intro m"
    ~line:6
    ~col:6
    ~kind:Binder
    ~pp_ty:"Nat"
    ~path:[ "m" ]
    ();
  (* hover on the intro `n` on the header line (line 6, col 8). *)
  assert_at
    ~idx
    ~source:filename
    ~label:"elim-header intro n"
    ~line:6
    ~col:8
    ~kind:Binder
    ~pp_ty:"Nat"
    ~path:[ "n" ]
    ();
  (* hover on the `\elim` target `m` (line 6, col 19) is a Use of type Nat,
     and goto-def lands on the header intro `m` at (6,6). *)
  assert_at
    ~idx
    ~source:filename
    ~label:"elim-header target m use"
    ~line:6
    ~col:19
    ~kind:Use
    ~pp_ty:"Nat"
    ~path:[ "m" ]
    ();
  assert_goto
    ~idx
    ~source:filename
    ~label:"elim-header target m goto intro"
    ~line:6
    ~col:19
    ~exp_line:6
    ~exp_col:6
    ();
  (* hover on a clause head `add` (line 7, col 4) is a Use carrying the
     function's type; goto-def jumps to the `\let` name token at (5,0). *)
  assert_at
    ~idx
    ~source:filename
    ~label:"elim-header clause-head use"
    ~line:7
    ~col:4
    ~kind:Use
    ~pp_ty:"(m : Nat) -> (n : Nat) -> Nat"
    ~path:[ "add" ]
    ();
  assert_goto
    ~idx
    ~source:filename
    ~label:"elim-header clause-head goto def"
    ~line:7
    ~col:4
    ~exp_line:5
    ~exp_col:5
    ()
;;

(* Hover types display through user-defined operator notation, with the raw
   form in a trailing `(i.e. …)`. *)
let notation_src =
  {|\universe U
\data Nat : U
  | zero : Nat
  | suc : Nat -> Nat
\data Id {A : U} (x : A) : A -> U
  | refl : Id x x
\operator "\x = \y" => Id x y
  \associativity: \left
\let z : Nat => zero
\let lemma (p : z = z) : Nat => zero
|}
;;

let test_notation_hover () =
  let filename = "test_notation.vt" in
  let idx = check_module_collecting ~filename notation_src in
  let open Violet_interactive.Index in
  (* let-param binder `p` in `(p : z = z)` — line 10, col 12 *)
  assert_at
    ~idx
    ~source:filename
    ~label:"hover notation-binder"
    ~line:10
    ~col:12
    ~kind:Binder
    ~pp_ty:"z = z (i.e. Id z z)"
    ~path:[ "p" ]
    ()
;;

(* \axioms command logic: deps_of filtered to exclude self.
   Elaborate a module with an axiom `axd_ua` and a let `axd_foo` that uses it,
   then assert the dependency tracking matches what handle_axioms relies on. *)
let test_axiom_deps () =
  Violet_elab.Axiom_deps.reset ();
  let src =
    {|\universe U
\axiom axd_ua : U
\let axd_foo : U => axd_ua
|}
  in
  let _idx = check_module_collecting ~filename:"test_axiom_deps.vt" src in
  (* names are complete Yuujinchou id paths; render "/"-joined for messages *)
  let show ps = String.concat ", " (List.map (String.concat "/") ps) in
  (* axd_foo depends on axd_ua (the axiom) *)
  let foo_deps = Violet_elab.Axiom_deps.deps_of [ "axd_foo" ] in
  if List.mem [ "axd_ua" ] foo_deps
  then Format.printf "axiom_deps OK  axd_foo depends on axd_ua@."
  else begin
    Format.printf "axiom_deps FAIL  axd_foo deps: [%s]@." (show foo_deps);
    exit 1
  end;
  (* handle_axioms display: filter out self — so display set for axd_foo excludes axd_foo *)
  let foo_display = Violet_elab.Axiom_deps.display_deps_of [ "axd_foo" ] in
  if foo_display = [ [ "axd_ua" ] ]
  then Format.printf "axiom_deps OK  axd_foo display set is [axd_ua]@."
  else begin
    Format.printf "axiom_deps FAIL  axd_foo display set: [%s]@." (show foo_display);
    exit 1
  end;
  (* axd_ua is an axiom: deps_of returns [axd_ua]; display excludes self => empty *)
  let ua_display = Violet_elab.Axiom_deps.display_deps_of [ "axd_ua" ] in
  if ua_display = []
  then
    Format.printf "axiom_deps OK  axd_ua display set is empty (no axiom dependencies)@."
  else begin
    Format.printf "axiom_deps FAIL  axd_ua display set: [%s]@." (show ua_display);
    exit 1
  end
;;

let () =
  test_elim_header_hover ();
  test_collector_roundtrip ();
  test_observer_emits_events ();
  test_find_at ();
  test_goto_definition ();
  test_goto_record_pun_collision ();
  test_goto_cross_module ();
  test_find_references ();
  test_goal_events ();
  test_hover_events ();
  test_notation_hover ();
  test_find_at_tiebreak ();
  test_axiom_deps ();
  Format.printf "all interactive tests passed@."
;;
