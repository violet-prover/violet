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

type t =
  { addrs : (string, string) Hashtbl.t (* addr -> source path (scrbl or .vt) *)
  ; dep_roots : (string * string) list (* (dep_key, "<dep_root>/src") *)
  }

let empty () = { addrs = Hashtbl.create 1; dep_roots = [] }

(* Direct deps of [proj], as [(key, "<dep_root>/src")] pairs. *)
let dep_roots_of (proj : Violet_project.Resolve.project) : (string * string) list =
  List.map
    (fun (k, (p : Violet_project.Resolve.project)) -> k, Filename.concat p.root "src")
    proj.dep_key_to_project
;;

(* Is [path] a source file under dep [src] (the dep's [src] directory)? *)
let under (src : string) (path : string) : bool =
  let pre = src ^ Filename.dir_sep in
  let n = String.length pre in
  String.length path >= n && String.equal (String.sub path 0 n) pre
;;

(* If [path] is a dep source, its dep-qualified address [key/<stem>]; else None. *)
let dep_addr_of_source (t : t) (path : string) : string option =
  match List.find_opt (fun (_k, src) -> under src path) t.dep_roots with
  | Some (k, _) -> Some (k ^ "/" ^ addr_of_path path)
  | None -> None
;;

(* Address of a definition's source file: dep-qualified for dep sources, a bare
   stem for the project's own cards. *)
let addr_of_source (t : t) (path : string) : string =
  match dep_addr_of_source t path with
  | Some a -> a
  | None -> addr_of_path path
;;

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

(* Scan [<root>/src] for every [*.vt.scrbl] card. [dep_roots] lets the registry
   recognise (and dep-qualify) definitions reached through dependencies. *)
let scan ~dep_roots ~root : t =
  let src = Filename.concat root "src" in
  let addrs = Hashtbl.create 16 in
  List.iter (fun f -> Hashtbl.replace addrs (addr_of_path f) f) (walk_scrbl src);
  { addrs; dep_roots }
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
