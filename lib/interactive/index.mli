module Trie = Yuujinchou.Trie

type entry_kind =
  | Def
  | Use
  | Goal
  | Binder

type entry =
  { path : Trie.path
  ; kind : entry_kind
  ; loc : Asai.Range.t
  ; def_loc : Asai.Range.t option
  ; def_target : Asai.Range.t option
  ; ty : Violet_kernel.Syntax.Core.value_ty option
  ; pp_ty : string option
  ; ctx : (string * string) list
  ; pp_target : string option
  ; axiom_deps : Trie.path list
  }

type t

val empty : t
val of_events : Violet_elab.Observer.event list -> t
val find_at : source:string -> line:int -> col:int -> t -> entry option
val def_of : entry -> t -> Asai.Range.t option
val all_entries : t -> entry list
val entries_at_path : Trie.path -> t -> entry list
val source_of_range : Asai.Range.t -> string option
