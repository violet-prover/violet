type definition_result =
  { path : string list
  ; loc : Asai.Range.t
  }

type reference =
  { loc : Asai.Range.t
  ; kind : Index.entry_kind
  }

let goto_definition ~source ~line ~col idx =
  match Index.find_at ~source ~line ~col idx with
  | None -> None
  | Some e ->
    (match Index.def_of e idx with
     | Some loc -> Some { path = e.path; loc }
     | None -> None)
;;

let find_references ~source ~line ~col idx =
  match Index.find_at ~source ~line ~col idx with
  | None -> []
  | Some e ->
    let all = Index.entries_at_path e.path idx in
    List.map (fun (d : Index.entry) -> { loc = d.loc; kind = d.kind }) all
;;
