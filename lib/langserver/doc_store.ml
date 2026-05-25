type doc =
  { uri : Linol_lsp.Lsp.Types.DocumentUri.t
  ; text : string
  ; version : int
  ; snapshot : Snapshot.t ref
  }

type t = (Linol_lsp.Lsp.Types.DocumentUri.t, doc) Hashtbl.t

let create () : t = Hashtbl.create 32

let module_path_of_uri uri =
  let path = Linol_lsp.Lsp.Types.DocumentUri.to_path uri in
  [ Filename.chop_extension (Filename.basename path) ]
;;

let update (t : t) ~uri ~text ~version : doc =
  match Hashtbl.find_opt t uri with
  | Some d ->
    let d = { d with text; version } in
    Hashtbl.replace t uri d;
    d
  | None ->
    let module_path = module_path_of_uri uri in
    let d = { uri; text; version; snapshot = ref (Snapshot.empty ~module_path) } in
    Hashtbl.add t uri d;
    d
;;

let find (t : t) ~uri : doc option = Hashtbl.find_opt t uri
let remove (t : t) ~uri : unit = Hashtbl.remove t uri
let iter (t : t) (f : doc -> unit) : unit = Hashtbl.iter (fun _ d -> f d) t

let%expect_test "create / update / find round-trip" =
  let t = create () in
  let uri = Linol_lsp.Lsp.Types.DocumentUri.of_path "/tmp/Foo.vt" in
  let _ = update t ~uri ~text:"" ~version:1 in
  (match find t ~uri with
   | Some d ->
     Printf.printf "v=%d mp=%s" d.version (String.concat "/" !(d.snapshot).module_path)
   | None -> Printf.printf "miss");
  [%expect {| v=1 mp=Foo |}]
;;

let%expect_test "update replaces text/version, keeps snapshot ref" =
  let t = create () in
  let uri = Linol_lsp.Lsp.Types.DocumentUri.of_path "/tmp/Bar.vt" in
  let d1 = update t ~uri ~text:"old" ~version:1 in
  let snap_ref = d1.snapshot in
  let d2 = update t ~uri ~text:"new" ~version:2 in
  Printf.printf
    "text=%s version=%d same_ref=%b"
    d2.text
    d2.version
    (snap_ref == d2.snapshot);
  [%expect {| text=new version=2 same_ref=true |}]
;;
