type mode =
  | Project of Resolve.project
  | Single_file of string

let module_name filename = Filename.chop_extension @@ Filename.basename filename

let rec walk_vt_files (dir : string) : string list =
  if not (Sys.file_exists dir)
  then []
  else
    Sys.readdir dir
    |> Array.to_list
    |> List.concat_map (fun entry ->
      if String.length entry > 0 && entry.[0] = '.'
      then []
      else if entry = "_build"
      then []
      else (
        let full = Filename.concat dir entry in
        if Sys.is_directory full
        then walk_vt_files full
        else if Filename.check_suffix entry ".vt"
        then [ full ]
        else []))
;;

let mode_for_entry ?explicit_root (filename : string) : mode =
  let mk_project root =
    try Project (Resolve.load root) with
    | Resolve.Project_error msg -> Violet_surface.Reporter.fatalf Parse_error "%s" msg
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
          (prefix_segs : string list)
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
