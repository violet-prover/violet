module IntMap = Map.Make (Int)

type entry_kind =
  | Def
  | Use
  | Goal
  | Binder

type entry =
  { path : string list
  ; kind : entry_kind
  ; loc : Asai.Range.t
  ; def_loc : Asai.Range.t option
  ; ty : Violet_kernel.Syntax.Core.value_ty option
  ; pp_ty : string option
  }

type t =
  { by_offset : entry list IntMap.t
  ; def_of : Asai.Range.t IntMap.t
  }

let start_offset (r : Asai.Range.t) : int =
  match Asai.Range.view r with
  | `Range (s, _) -> s.offset
  | `End_of_file p -> p.offset
;;

let empty = { by_offset = IntMap.empty; def_of = IntMap.empty }

let entry_of_event : Violet_elab.Observer.event -> entry = function
  | Violet_elab.Observer.Def { path; loc; ty; pp_ty } ->
    { path; kind = Def; loc; def_loc = Some loc; ty = Some ty; pp_ty = Some pp_ty }
  | Violet_elab.Observer.Use { path; loc; def_loc; ty; pp_ty } ->
    { path; kind = Use; loc; def_loc; ty = Some ty; pp_ty = Some pp_ty }
  | Violet_elab.Observer.Goal { path; loc; ty; _ } ->
    { path; kind = Goal; loc; def_loc = None; ty = Some ty; pp_ty = None }
  | Violet_elab.Observer.Binder { path; loc } ->
    { path; kind = Binder; loc; def_loc = Some loc; ty = None; pp_ty = None }
;;

let of_events evs =
  let entries = List.map entry_of_event evs in
  let by_offset =
    List.fold_left
      (fun m e ->
         let key = start_offset e.loc in
         let existing =
           match IntMap.find_opt key m with
           | Some l -> l
           | None -> []
         in
         IntMap.add key (e :: existing) m)
      IntMap.empty
      entries
  in
  let defs_by_path =
    List.fold_left
      (fun m e ->
         match e.kind with
         | Def -> (e.path, e.loc) :: m
         | _ -> m)
      []
      entries
  in
  let def_of =
    List.fold_left
      (fun m e ->
         match e.def_loc with
         | Some loc -> IntMap.add (start_offset e.loc) loc m
         | None ->
           (match List.assoc_opt e.path defs_by_path with
            | Some def_loc -> IntMap.add (start_offset e.loc) def_loc m
            | None -> m))
      IntMap.empty
      entries
  in
  { by_offset; def_of }
;;

let pos_in_range ~line ~col (r : Asai.Range.t) : bool =
  match Asai.Range.view r with
  | `Range (s, e) ->
    let s_col = s.offset - s.start_of_line in
    let e_col = e.offset - e.start_of_line in
    (line > s.line_num || (line = s.line_num && col >= s_col))
    && (line < e.line_num || (line = e.line_num && col <= e_col))
  | `End_of_file _ -> false
;;

let range_width (r : Asai.Range.t) : int =
  match Asai.Range.view r with
  | `Range (s, e) -> e.offset - s.offset
  | `End_of_file _ -> max_int
;;

let source_of_range (r : Asai.Range.t) : string option =
  match Asai.Range.view r with
  | `Range (s, _) ->
    (match s.source with
     | `File f -> Some f
     | `String _ -> None)
  | `End_of_file s ->
    (match s.source with
     | `File f -> Some f
     | `String _ -> None)
;;

let find_at ~source ~line ~col t =
  let best = ref None in
  IntMap.iter
    (fun _ es ->
       List.iter
         (fun e ->
            if pos_in_range ~line ~col e.loc
            then (
              match source_of_range e.loc with
              | Some f when String.equal f source ->
                (match !best with
                 | None -> best := Some e
                 | Some b -> if range_width e.loc < range_width b.loc then best := Some e)
              | _ -> ()))
         es)
    t.by_offset;
  !best
;;

let def_of entry t = IntMap.find_opt (start_offset entry.loc) t.def_of
let all_entries t = IntMap.fold (fun _ es acc -> List.rev_append es acc) t.by_offset []

let entries_at_path path t =
  IntMap.fold
    (fun _ es acc ->
       List.fold_left (fun acc e -> if e.path = path then e :: acc else acc) acc es)
    t.by_offset
    []
;;
