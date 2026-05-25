let parse_string ~filename src =
  let lexbuf = Lexing.from_string src in
  let toks = Array.of_list (Violet_elab.Parser.tokens filename lexbuf) in
  Violet_elab.Parser.parse_buf ~name:filename toks
;;

let with_handlers k =
  Violet_elab.Reporter.run
    ~emit:(fun _ -> ())
    ~fatal:(fun d ->
      failwith
        (Format.asprintf
           "%s: %t"
           (Violet_elab.Reporter.Message.show d.message)
           d.explanation.value))
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

let test_goto_definition () =
  let src =
    {|\universe U
\let myconst (A : U) (B : U) (x : A) (y : B) : A => x
|}
  in
  let filename = "test_goto_def.vt" in
  let idx = check_module_collecting ~filename src in
  let defs =
    List.filter
      (fun (e : Violet_interactive.Index.entry) -> e.kind = Def)
      (Violet_interactive.Index.all_entries idx)
  in
  if List.exists (fun (e : Violet_interactive.Index.entry) -> e.path = [ "myconst" ]) defs
  then Format.printf "goto_definition OK  'myconst' def exists@."
  else begin
    Format.printf "goto_definition FAIL  no 'myconst' def@.";
    exit 1
  end
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

let () =
  test_collector_roundtrip ();
  test_observer_emits_events ();
  test_find_at ();
  test_goto_definition ();
  test_find_references ();
  test_goal_events ();
  Format.printf "all interactive tests passed@."
;;
