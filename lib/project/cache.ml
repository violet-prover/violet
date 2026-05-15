let cache_root () =
  let home =
    try Sys.getenv "HOME" with
    | Not_found -> failwith "HOME is not set"
  in
  Filename.concat home ".cache/violet/git"
;;

let url_hash (url : string) : string = Digest.to_hex (Digest.string url)

let dep_dir ~url ~rev : string =
  Filename.concat (Filename.concat (cache_root ()) (url_hash url)) rev
;;

let rec mkdir_p p =
  if Sys.file_exists p
  then ()
  else begin
    mkdir_p (Filename.dirname p);
    Unix.mkdir p 0o755
  end
;;

let ensure_clone ~url ~rev : string =
  let d = dep_dir ~url ~rev in
  if Sys.file_exists (Filename.concat d "info.vt")
  then d
  else begin
    mkdir_p (Filename.dirname d);
    (* shallow clone, then checkout the rev *)
    let q s = Filename.quote s in
    let cmd =
      Printf.sprintf
        "git clone --quiet %s %s && git -C %s checkout --quiet %s"
        (q url)
        (q d)
        (q d)
        (q rev)
    in
    let status = Sys.command cmd in
    if status <> 0 then failwith (Printf.sprintf "git clone failed: %s @ %s" url rev);
    d
  end
;;
