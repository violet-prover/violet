open Manifest_lexer

type entry =
  { key : string
  ; url : string
  ; rev : string
  }
[@@deriving show]

type t = { entries : entry list } [@@deriving show]

let parse_string (s : string) : t =
  let st = Manifest.make_state s in
  let entries = ref [] in
  let rec loop () =
    match st.cur with
    | EOF -> ()
    | LOCKED ->
      Manifest.advance st;
      let key = Manifest.expect_ident st in
      let attrs = Manifest.parse_attrs st in
      let url =
        match List.assoc_opt "git" attrs with
        | Some u -> u
        | None -> failwith "\\locked: missing git"
      in
      let rev =
        match List.assoc_opt "rev" attrs with
        | Some r -> r
        | None -> failwith "\\locked: missing rev"
      in
      entries := { key; url; rev } :: !entries;
      loop ()
    | t ->
      failwith
        (Printf.sprintf "lockfile: unexpected token %s" (Manifest_lexer.show_token t))
  in
  loop ();
  { entries = List.rev !entries }
;;

let%expect_test "parse lockfile" =
  let lk =
    parse_string
      {|
    \locked stdlib (git = "https://example/repo", rev = "abc123")
  |}
  in
  Printf.printf "entries=%d\n" (List.length lk.entries);
  List.iter (fun e -> Printf.printf "%s %s %s\n" e.key e.url e.rev) lk.entries;
  [%expect
    {|
    entries=1
    stdlib https://example/repo abc123
    |}]
;;

let to_string (lk : t) : string =
  let buf = Buffer.create 256 in
  List.iter
    (fun e ->
       Buffer.add_string
         buf
         (Printf.sprintf "\\locked %s (git = %S, rev = %S)\n" e.key e.url e.rev))
    lk.entries;
  Buffer.contents buf
;;

let%expect_test "lockfile round-trips" =
  let lk = { entries = [ { key = "a"; url = "https://x"; rev = "r1" } ] } in
  let s = to_string lk in
  let lk' = parse_string s in
  Printf.printf "%b" (lk = lk');
  [%expect {| true |}]
;;
