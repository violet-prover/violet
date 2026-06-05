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
  ; def_target : Asai.Range.t option
  ; ty : Violet_kernel.Syntax.Core.value_ty option
  ; pp_ty : string option
  ; ctx : (string * string) list
  ; pp_target : string option
  }

type t = { by_offset : entry list IntMap.t }

let start_offset = Violet_common.Range.start_offset
let source_of_range = Violet_common.Range.source
let empty = { by_offset = IntMap.empty }

(* The module path of a Def event (segments of the emitting module); other
   events carry no module path. *)
let module_path_of_event : Violet_elab.Observer.event -> string list = function
  | Violet_elab.Observer.Def { module_path; _ } -> module_path
  | _ -> []
;;

let entry_of_event : Violet_elab.Observer.event -> entry = function
  | Violet_elab.Observer.Def { path; module_path = _; loc; name_loc; ty; pp_ty } ->
    { path
    ; kind = Def
    ; loc
    ; def_loc = Some (Option.value name_loc ~default:loc)
    ; def_target = None
    ; ty = Some ty
    ; pp_ty = Some pp_ty
    ; ctx = []
    ; pp_target = None
    }
  | Violet_elab.Observer.Use { path; loc; def_loc; ty; pp_ty } ->
    { path
    ; kind = Use
    ; loc
    ; def_loc
    ; def_target = None
    ; ty = Some ty
    ; pp_ty = Some pp_ty
    ; ctx = []
    ; pp_target = None
    }
  | Violet_elab.Observer.Goal { path; loc; ty; ctx; pp_target } ->
    { path
    ; kind = Goal
    ; loc
    ; def_loc = None
    ; def_target = None
    ; ty = Some ty
    ; pp_ty = None
    ; ctx
    ; pp_target = Some pp_target
    }
  | Violet_elab.Observer.Binder { path; loc; ty; pp_ty } ->
    { path
    ; kind = Binder
    ; loc
    ; def_loc = Some loc
    ; def_target = None
    ; ty
    ; pp_ty
    ; ctx = []
    ; pp_target = None
    }
;;

let is_multiline = Violet_common.Range.is_multiline

(* Resolve a Use/Goal whose own event carried no [def_loc] via the bare-path
   fallback. [candidates] are the (target_loc) of every Def registered under
   the entry's path. Collision resolution: prefer a Def in the same source
   file as the use; if still several (or none same-file), the first registered.
   Only Def entries populate the fallback table — local binders must not, or a
   bare name `x` would jump to a same-named binder in another definition. *)
let resolve_fallback ~(use_loc : Asai.Range.t) (candidates : Asai.Range.t list)
  : Asai.Range.t option
  =
  match candidates with
  | [] -> None
  | [ single ] -> Some single
  | _ ->
    let use_src = source_of_range use_loc in
    let same_file =
      match use_src with
      | None -> []
      | Some f ->
        List.filter
          (fun c ->
             match source_of_range c with
             | Some cf -> String.equal cf f
             | None -> false)
          candidates
    in
    (match same_file with
     | hit :: _ -> Some hit
     | [] -> Some (List.hd candidates))
;;

let of_events evs =
  let entries =
    List.filter_map
      (fun ev ->
         let e = entry_of_event ev in
         match e.kind with
         (* A Use spanning multiple lines, or a Binder whose name span is
            multiline, is inherited synthesis provenance noise (a binder NAME
            is never multiline in the source). Drop both. Def/Goal are kept
            as-is. *)
         | (Use | Binder) when is_multiline e.loc -> None
         | _ -> Some e)
      evs
  in
  (* Bare-name → Def target locs. Each Def is registered under BOTH its own
     path and module_path @ path, so qualified uses (`mymod/foo`, two-segment
     ctor/field names) resolve. Built from the raw events so module_path is
     available. Registration order is preserved per key (first registered wins
     ties). *)
  let defs_by_path =
    List.fold_left
      (fun acc ev ->
         match ev with
         | Violet_elab.Observer.Def _ ->
           let e = entry_of_event ev in
           let target = Option.value e.def_loc ~default:e.loc in
           let module_path = module_path_of_event ev in
           let acc = (e.path, target) :: acc in
           let qualified = module_path @ e.path in
           if qualified <> e.path then (qualified, target) :: acc else acc
         | _ -> acc)
      []
      evs
  in
  (* Candidates for a path, in registration order (defs_by_path is built
     reversed by the left fold, so reverse to recover it). *)
  let defs_by_path = List.rev defs_by_path in
  let candidates_for path =
    List.filter_map (fun (p, l) -> if p = path then Some l else None) defs_by_path
  in
  let resolve_target (e : entry) : Asai.Range.t option =
    match e.def_loc with
    | Some _ as l -> l
    | None -> resolve_fallback ~use_loc:e.loc (candidates_for e.path)
  in
  let entries = List.map (fun e -> { e with def_target = resolve_target e }) entries in
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
  { by_offset }
;;

let pos_in_range = Violet_common.Range.pos_in_range
let range_width = Violet_common.Range.width

let find_at ~source ~line ~col t =
  let best = ref None in
  let is_binder (e : entry) = e.kind = Binder in
  (* Narrowest span wins; on EQUAL width, a non-Binder entry beats a Binder
     entry (so a record field Use/Def reported through synthesized binder
     provenance does not shadow the real token). *)
  let better (e : entry) (b : entry) =
    let we = range_width e.loc
    and wb = range_width b.loc in
    we < wb || (we = wb && is_binder b && not (is_binder e))
  in
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
                 | Some b -> if better e b then best := Some e)
              | _ -> ()))
         es)
    t.by_offset;
  !best
;;

let def_of entry _t = entry.def_target
let all_entries t = IntMap.fold (fun _ es acc -> List.rev_append es acc) t.by_offset []

let entries_at_path path t =
  IntMap.fold
    (fun _ es acc ->
       List.fold_left (fun acc e -> if e.path = path then e :: acc else acc) acc es)
    t.by_offset
    []
;;
