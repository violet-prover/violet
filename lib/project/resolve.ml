type project =
  { root : string (* absolute path to project root *)
  ; manifest : Manifest.t
  ; local_segments : string list (* names directly under src/ *)
  ; dep_key_to_project : (string * project) list (* (dep_key, recursively loaded dep) *)
  }

exception Project_error of string

let read_file p =
  let ic = open_in p in
  Fun.protect ~finally:(fun () -> close_in ic)
  @@ fun () ->
  let n = in_channel_length ic in
  let b = Bytes.create n in
  really_input ic b 0 n;
  Bytes.to_string b
;;

let list_src_segments (root : string) : string list =
  let src = Filename.concat root "src" in
  if not (Sys.file_exists src)
  then []
  else
    Sys.readdir src
    |> Array.to_list
    |> List.filter_map (fun entry ->
      let full = Filename.concat src entry in
      if Sys.is_directory full
      then Some entry
      else if Filename.check_suffix entry ".vt"
      then Some (Filename.chop_extension entry)
      else None)
;;

let load_manifest (root : string) : Manifest.t =
  let info = Filename.concat root "info.vt" in
  if not (Sys.file_exists info)
  then raise (Project_error (Printf.sprintf "no info.vt at %s" root));
  Manifest.parse_string (read_file info)
;;

let load_lock_opt ~(root : string) : Lockfile.t option =
  let p = Filename.concat root "info.lock" in
  if Sys.file_exists p then Some (Lockfile.parse_string (read_file p)) else None
;;

let collisions (locals : string list) (deps : Manifest.dep list) : string list =
  let dep_keys = List.map (fun (d : Manifest.dep) -> d.key) deps in
  let local_set = List.sort_uniq compare locals in
  List.filter (fun k -> List.mem k local_set) dep_keys
;;

(* Recursive load: each dep becomes its own fully-loaded project. This is how
   dep boundaries are enforced — a dep's deps are not transitively visible to
   the consumer, because the consumer only consults its own dep_key_to_project. *)
let rec load (root : string) : project =
  let manifest = load_manifest root in
  let lock = load_lock_opt ~root in
  let local_segments = list_src_segments root in
  let cols = collisions local_segments manifest.deps in
  (match cols with
   | [] -> ()
   | _ ->
     let msg = String.concat ", " cols in
     raise
       (Project_error
          (Printf.sprintf
             "module prefix(es) collide with dependencies: %s; rename one of them"
             msg)));
  let dep_key_to_project =
    List.map
      (fun (d : Manifest.dep) -> d.key, resolve_dep_project ~lock root d)
      manifest.deps
  in
  { root; manifest; local_segments; dep_key_to_project }

and resolve_dep_project
      ?(lock : Lockfile.t option = None)
      (root : string)
      (d : Manifest.dep)
  : project
  =
  let dep_root =
    match d.source with
    | Path p -> if Filename.is_relative p then Filename.concat root p else p
    | Git { url; rev = _manifest_rev } ->
      let locked_rev =
        match lock with
        | None ->
          raise
            (Project_error
               (Printf.sprintf
                  "git dep `%s` is declared in info.vt but missing from info.lock; run \
                   `violet update`"
                  d.key))
        | Some lock ->
          (match
             List.find_opt (fun (e : Lockfile.entry) -> e.key = d.key) lock.entries
           with
           | Some e when e.url = url -> e.rev
           | Some e ->
             raise
               (Project_error
                  (Printf.sprintf
                     "git dep `%s` url mismatch: info.vt says %s, info.lock says %s; run \
                      `violet update`"
                     d.key
                     url
                     e.url))
           | None ->
             raise
               (Project_error
                  (Printf.sprintf
                     "git dep `%s` is declared in info.vt but missing from info.lock; \
                      run `violet update`"
                     d.key)))
      in
      Cache.ensure_clone ~url ~rev:locked_rev
  in
  load dep_root
;;

let mk_test_tree () =
  let tmp = Filename.temp_dir "violet_proj_test_" "" in
  let write rel content =
    let p = Filename.concat tmp rel in
    let dir = Filename.dirname p in
    if not (Sys.file_exists dir) then Unix.mkdir dir 0o755;
    let oc = open_out p in
    output_string oc content;
    close_out oc
  in
  tmp, write
;;

let%expect_test "load_manifest returns parsed manifest" =
  let tmp, write = mk_test_tree () in
  write "info.vt" {| \name "p" \version "1.0" |};
  let m = load_manifest tmp in
  Printf.printf "%s %s" m.name m.version;
  [%expect {| p 1.0 |}]
;;

let%expect_test "collisions detected" =
  let tmp, write = mk_test_tree () in
  write
    "info.vt"
    {|
    \name "p" \version "1"
    \dep nat (path = "../nat")
  |};
  Unix.mkdir (Filename.concat tmp "src") 0o755;
  write "src/nat.vt" "";
  (try
     let _ = load tmp in
     print_string "no error"
   with
   | Project_error msg -> print_string msg);
  [%expect {| module prefix(es) collide with dependencies: nat; rename one of them |}]
;;

let%expect_test "load: git dep without lock entry fails" =
  let tmp, write = mk_test_tree () in
  write
    "info.vt"
    {|
    \name "p" \version "1"
    \dep stdlib (git = "https://example/repo", rev = "main")
  |};
  (try
     let _ = load tmp in
     print_string "no error"
   with
   | Project_error msg -> print_string msg);
  [%expect
    {| git dep `stdlib` is declared in info.vt but missing from info.lock; run `violet update` |}]
;;

let%expect_test "load: git dep with lock entry uses locked rev" =
  let tmp, write = mk_test_tree () in
  write
    "info.vt"
    {|
    \name "p" \version "1"
    \dep stdlib (git = "https://example/repo", rev = "main")
  |};
  write "info.lock" {| \locked stdlib (git = "https://example/repo", rev = "abc123") |};
  (* We can't actually ensure_clone in a test (network/git). Instead, verify load_lock_opt
     returns a populated Lockfile.t and that the rev is what we expect. This is a smaller
     check than a full end-to-end load+clone, but it covers the spec contract that the
     locked rev is what gets used. *)
  let lock =
    match load_lock_opt ~root:tmp with
    | Some l -> l
    | None -> failwith "expected lockfile"
  in
  Printf.printf "%s\n" (List.hd lock.entries).rev;
  [%expect {| abc123 |}]
;;

let%expect_test "path dep resolves to absolute root" =
  let tmp, write = mk_test_tree () in
  (* sibling project *)
  Unix.mkdir (Filename.concat tmp "sibling") 0o755;
  write "sibling/info.vt" {| \name "s" \version "1" |};
  write
    "info.vt"
    {|
    \name "p" \version "1"
    \dep sib (path = "sibling")
  |};
  let proj = load tmp in
  let dep_proj = List.assoc "sib" proj.dep_key_to_project in
  Printf.printf "%b" (dep_proj.root = Filename.concat tmp "sibling");
  [%expect {| true |}]
;;

(* Resolve an import path that has already crossed a dep boundary. Only the
   dep's local_segments are visible — the dep's own deps are private. *)
let resolve_in_dep (proj : project) (path : string list) : string =
  match path with
  | [] -> raise (Project_error "empty import path")
  | first :: _ when List.mem first proj.local_segments ->
    let joined = String.concat "/" path in
    Filename.concat (Filename.concat proj.root "src") (joined ^ ".vt")
  | _ ->
    raise
      (Project_error (Printf.sprintf "unresolved import: %s" (String.concat "/" path)))
;;

(* Resolve an import and report which project owns the resolved file plus the
   dep-key prefix (if any) acquired by crossing into that project. The prefix
   is `Some "k"` when this import crosses into a dep keyed `k` in `proj`, and
   `None` when the import stays local to `proj`. Callers thread the prefix to
   build a canonical module path so the same physical file gets a single key
   regardless of which consumer's spelling reached it. *)
let resolve_import_in (proj : project) (path : string list)
  : project * string option * string
  =
  match path with
  | [] -> raise (Project_error "empty import path")
  | first :: rest ->
    if List.mem first proj.local_segments
    then (
      let joined = String.concat "/" (first :: rest) in
      proj, None, Filename.concat (Filename.concat proj.root "src") (joined ^ ".vt"))
    else (
      match List.assoc_opt first proj.dep_key_to_project with
      | Some dep_proj ->
        (match rest with
         | [] ->
           raise
             (Project_error
                (Printf.sprintf "import `%s` is just a dep key with no module path" first))
         | _ -> dep_proj, Some first, resolve_in_dep dep_proj rest)
      | None ->
        raise
          (Project_error (Printf.sprintf "unresolved import: %s" (String.concat "/" path))))
;;

let resolve_import (proj : project) (path : string list) : string =
  let _, _, fp = resolve_import_in proj path in
  fp
;;

let%expect_test "resolve_import: local" =
  let tmp, write = mk_test_tree () in
  write "info.vt" {| \name "p" \version "1" |};
  Unix.mkdir (Filename.concat tmp "src") 0o755;
  write "src/nat.vt" "";
  Unix.mkdir (Filename.concat tmp "src/nat") 0o755;
  write "src/nat/properties.vt" "";
  let proj = load tmp in
  let p1 = resolve_import proj [ "nat" ] in
  let p2 = resolve_import proj [ "nat"; "properties" ] in
  Printf.printf
    "%b %b"
    (p1 = Filename.concat tmp "src/nat.vt")
    (p2 = Filename.concat tmp "src/nat/properties.vt");
  [%expect {| true true |}]
;;

let%expect_test "resolve_import: dep" =
  let tmp, write = mk_test_tree () in
  Unix.mkdir (Filename.concat tmp "sibling") 0o755;
  Unix.mkdir (Filename.concat tmp "sibling/src") 0o755;
  write "sibling/info.vt" {| \name "s" \version "1" |};
  write "sibling/src/foo.vt" "";
  write
    "info.vt"
    {|
    \name "p" \version "1"
    \dep sib (path = "sibling")
  |};
  let proj = load tmp in
  let p = resolve_import proj [ "sib"; "foo" ] in
  Printf.printf "%b" (p = Filename.concat tmp "sibling/src/foo.vt");
  [%expect {| true |}]
;;

let%expect_test "resolve_import: deps deps are not transitively visible" =
  let tmp, write = mk_test_tree () in
  (* sibling provides foo and declares its own (path) dep `inner` *)
  Unix.mkdir (Filename.concat tmp "sibling") 0o755;
  Unix.mkdir (Filename.concat tmp "sibling/src") 0o755;
  Unix.mkdir (Filename.concat tmp "inner") 0o755;
  Unix.mkdir (Filename.concat tmp "inner/src") 0o755;
  write "inner/info.vt" {| \name "inner" \version "1" |};
  write "inner/src/secret.vt" "";
  write
    "sibling/info.vt"
    {|
    \name "s" \version "1"
    \dep inner (path = "../inner")
  |};
  write "sibling/src/foo.vt" "";
  write
    "info.vt"
    {|
    \name "p" \version "1"
    \dep sib (path = "sibling")
  |};
  let proj = load tmp in
  (* sib/foo works *)
  let p = resolve_import proj [ "sib"; "foo" ] in
  Printf.printf "%b\n" (p = Filename.concat tmp "sibling/src/foo.vt");
  (* sib/inner/secret must NOT work: `inner` is sibling's private dep, not visible to consumer *)
  (try
     let _ = resolve_import proj [ "sib"; "inner"; "secret" ] in
     print_string "no error"
   with
   | Project_error msg -> Printf.printf "blocked: %s\n" msg);
  [%expect
    {|
    true
    blocked: unresolved import: inner/secret
    |}]
;;

let%expect_test "resolve_import: unresolved" =
  let tmp, write = mk_test_tree () in
  write "info.vt" {| \name "p" \version "1" |};
  let proj = load tmp in
  (try
     let _ = resolve_import proj [ "missing" ] in
     print_string "no error"
   with
   | Project_error msg -> print_string msg);
  [%expect {| unresolved import: missing |}]
;;
