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

let read_head_sha (dir : string) : string =
  let cmd = Printf.sprintf "git -C %s rev-parse HEAD" (Filename.quote dir) in
  let ic = Unix.open_process_in cmd in
  let line =
    try input_line ic with
    | End_of_file -> ""
  in
  match Unix.close_process_in ic with
  | Unix.WEXITED 0 -> String.trim line
  | _ -> failwith (Printf.sprintf "git rev-parse HEAD failed in %s" dir)
;;

(* Ensure a clone of `url` checked out at `rev` exists in the cache, and return
   `(dir, sha)` where `sha` is the resolved commit SHA at HEAD. Cache is keyed
   by the resolved SHA: if `rev` was a branch or tag, we re-key after cloning so
   later calls (which pass the SHA from info.lock) hit the same directory. *)
let ensure_clone ~url ~rev : string * string =
  let by_rev = dep_dir ~url ~rev in
  if Sys.file_exists (Filename.concat by_rev "info.vt")
  then by_rev, read_head_sha by_rev
  else begin
    mkdir_p (Filename.dirname by_rev);
    let q s = Filename.quote s in
    let cmd =
      Printf.sprintf
        "git clone --quiet %s %s && git -C %s checkout --quiet %s"
        (q url)
        (q by_rev)
        (q by_rev)
        (q rev)
    in
    let status = Sys.command cmd in
    if status <> 0 then failwith (Printf.sprintf "git clone failed: %s @ %s" url rev);
    let sha = read_head_sha by_rev in
    if sha = rev
    then by_rev, sha
    else begin
      let by_sha = dep_dir ~url ~rev:sha in
      if Sys.file_exists by_sha
      then begin
        let _ = Sys.command (Printf.sprintf "rm -rf %s" (q by_rev)) in
        by_sha, sha
      end
      else begin
        mkdir_p (Filename.dirname by_sha);
        Unix.rename by_rev by_sha;
        by_sha, sha
      end
    end
  end
;;
