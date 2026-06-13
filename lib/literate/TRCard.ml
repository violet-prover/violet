(* The set of literate files in a project, used to resolve cross-card
   goto-definition. A card's *address* is its filename stem (matching
   tr-notes' [/<addr>] URL scheme): [content/foo.vt.scrbl] and the synthetic
   module path [content/foo.vt] both have address [foo]. *)

let tr_card_suffix = ".vt.scrbl"

(* Address of any path that might name a card: strip [.vt.scrbl] or [.vt]. A
   definition's source range may carry either form (a card parsed as the primary
   document uses its [.vt] module path; the same card parsed as a dependency is
   resolved through the loader to a [.vt] path too), so both normalize here. *)
let addr_of_path (path : string) : string =
  let base = Filename.basename path in
  if Filename.check_suffix base tr_card_suffix
  then String.sub base 0 (String.length base - String.length tr_card_suffix)
  else if Filename.check_suffix base ".vt"
  then Filename.chop_extension base
  else base
;;

type t = { addrs : (string, string) Hashtbl.t (* addr -> scrbl path *) }

let empty () = { addrs = Hashtbl.create 1 }

let rec walk_scrbl (dir : string) : string list =
  if not (Sys.file_exists dir)
  then []
  else
    Sys.readdir dir
    |> Array.to_list
    |> List.concat_map (fun entry ->
      if String.length entry > 0 && entry.[0] = '.'
      then []
      else if entry = "_build" || entry = "_tmp"
      then []
      else (
        let full = Filename.concat dir entry in
        if Sys.is_directory full
        then walk_scrbl full
        else if Filename.check_suffix entry tr_card_suffix
        then [ full ]
        else []))
;;

(* Scan [<root>/src] for every [*.vt.scrbl] card. *)
let scan ~root : t =
  let src = Filename.concat root "src" in
  let addrs = Hashtbl.create 16 in
  List.iter (fun f -> Hashtbl.replace addrs (addr_of_path f) f) (walk_scrbl src);
  { addrs }
;;

(* Register a card explicitly. Used to add the card being woven so its own
   in-page jumps resolve even in single-file mode (no project scan). *)
let add (t : t) ~(addr : string) ~(path : string) : unit =
  Hashtbl.replace t.addrs addr path
;;

let mem (t : t) (addr : string) : bool = Hashtbl.mem t.addrs addr

let cards (t : t) : (string * string) list =
  Hashtbl.fold (fun a p acc -> (a, p) :: acc) t.addrs []
;;
