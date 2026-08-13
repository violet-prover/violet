module Trie = Yuujinchou.Trie
open Violet_common

type mode =
  | Project of Resolve.project
  | Single_file of string

let module_name filename = Filename.chop_extension @@ Filename.basename filename

(* [dir]'s files as git already knows them — tracked, or untracked-but-not-
   ignored — via one [git ls-files] call, so ignore semantics ([.gitignore],
   [.git/info/exclude], nested per-directory rules, [core.excludesfile]) are
   git's own, not reimplemented here. [None] when [dir] isn't inside a git
   work tree (no [git] on PATH counts as "not inside one" too). Paths in the
   output are relative to [dir] (that's what [-C dir] with no pathspec
   scopes to) and are joined back onto [dir] before returning. *)
let git_tracked_files (dir : string) : string list option =
  let ic =
    Unix.open_process_in
      (Printf.sprintf
         "git -C %s ls-files --cached --others --exclude-standard 2>/dev/null"
         (Filename.quote dir))
  in
  let lines = In_channel.input_lines ic in
  match Unix.close_process_in ic with
  | Unix.WEXITED 0 -> Some (List.map (Filename.concat dir) lines)
  | _ -> None
;;

(* Recursively walk [dir], yielding every full path an entry-level [keep]
   accepts. Prefers [git_tracked_files] (correct gitignore semantics, one
   process for the whole subtree) when [dir] is inside a git work tree;
   otherwise falls back to a plain [Sys.readdir] walk that skips dotfiles and
   any [_]-prefixed directory (the convention dune's own [_build] follows:
   [_fetch]/[_private]/[_release]/[_tmp]/...), on the assumption that a
   non-git project's scratch/generated directories follow it too. Shared by
   every project file-discovery pass ([walk_vt_files] below;
   [Violet_literate.Weave]'s whole-project card discovery) so only the
   per-entry predicate differs. *)
let rec walk_files ~(keep : string -> bool) (dir : string) : string list =
  if not (Sys.file_exists dir)
  then []
  else (
    match git_tracked_files dir with
    | Some files -> List.filter (fun f -> keep (Filename.basename f)) files
    | None ->
      Sys.readdir dir
      |> Array.to_list
      |> List.concat_map (fun entry ->
        if String.length entry > 0 && (entry.[0] = '.' || entry.[0] = '_')
        then []
        else (
          let full = Filename.concat dir entry in
          if Sys.is_directory full
          then walk_files ~keep full
          else if keep entry
          then [ full ]
          else [])))
;;

let walk_vt_files (dir : string) : string list =
  walk_files ~keep:(fun entry -> Filename.check_suffix entry ".vt") dir
;;

let mode_for_entry ?explicit_root (filename : string) : mode =
  let mk_project root =
    try Project (Resolve.load root) with
    | Resolve.Project_error msg -> Reporter.fatalf Parse_error "%s" msg
  in
  match explicit_root with
  | Some root -> mk_project root
  | None ->
    let start =
      let full =
        if Filename.is_relative filename
        then Filename.concat (Sys.getcwd ()) filename
        else filename
      in
      Filename.dirname full
    in
    (match Root.find_root start with
     | Some root -> mk_project root
     | None -> Single_file (Filename.dirname filename))
;;

type dependencies = (string, string list) Hashtbl.t
type modules = (string, Violet_surface.Surface.t) Hashtbl.t

let rec prepare_dependencies
          ?(text_override = fun _ -> None)
          (mode : mode)
          (prefix_segs : Trie.path)
          (mods : modules)
          (deps : dependencies)
          (key : string)
          (m : Violet_surface.Surface.t)
  =
  if Hashtbl.mem deps key
  then ()
  else begin
    let canonical_libraries = List.map (fun lib -> prefix_segs @ lib) m.imports in
    Hashtbl.add mods key { m with imports = canonical_libraries };
    Hashtbl.add deps key (List.map (String.concat "/") canonical_libraries);
    List.iter2
      (fun user_library canonical_library ->
         let canonical_key = String.concat "/" canonical_library in
         let next_mode, next_segs, filepath =
           match mode with
           | Project proj ->
             let p, crossed, fp = Resolve.resolve_import_in proj user_library in
             let ns =
               match crossed with
               | Some k -> prefix_segs @ [ k ]
               | None -> prefix_segs
             in
             Project p, ns, fp
           | Single_file root ->
             ( mode
             , prefix_segs
             , Filename.concat root (String.concat "/" user_library ^ ".vt") )
         in
         let m =
           match text_override filepath with
           | Some text -> Violet_surface.Parser.parse_buffer ~filename:filepath text
           | None -> Violet_surface.Parser.parse_file filepath
         in
         prepare_dependencies ~text_override next_mode next_segs mods deps canonical_key m)
      m.imports
      canonical_libraries
  end
;;
