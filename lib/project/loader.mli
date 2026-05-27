type mode =
  | Project of Resolve.project
  | Single_file of string

val module_name : string -> string
val walk_vt_files : string -> string list
val mode_for_entry : ?explicit_root:string -> string -> mode

type dependencies = (string, string list) Hashtbl.t
type modules = (string, Violet_surface.Surface.t) Hashtbl.t

val prepare_dependencies
  :  ?text_override:(string -> string option)
  -> mode
  -> string list
  -> modules
  -> dependencies
  -> string
  -> Violet_surface.Surface.t
  -> unit
