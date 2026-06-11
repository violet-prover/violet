module Trie = Yuujinchou.Trie

type event =
  | Def of
      { path : Trie.path
      ; module_path : Trie.path
      ; loc : Asai.Range.t
      ; name_loc : Asai.Range.t option
      ; ty : Violet_kernel.Syntax.Core.value_ty
      ; pp_ty : string
      ; (* Axioms this definition transitively depends on (self excluded),
           each as its complete Yuujinchou id. *)
        axiom_deps : Trie.path list
      }
  | Use of
      { path : Trie.path
      ; loc : Asai.Range.t
      ; def_loc : Asai.Range.t option
      ; ty : Violet_kernel.Syntax.Core.value_ty
      ; pp_ty : string
      }
  | Goal of
      { path : Trie.path
      ; loc : Asai.Range.t
      ; ty : Violet_kernel.Syntax.Core.value_ty
      ; ctx : (string * string) list
      ; pp_target : string
      }
  | Binder of
      { path : Trie.path
      ; loc : Asai.Range.t
      ; ty : Violet_kernel.Syntax.Core.value_ty option
      ; pp_ty : string option
      }

val emit : event -> unit
val run : on_event:(event -> unit) -> (unit -> 'a) -> 'a
val run_silent : (unit -> 'a) -> 'a
