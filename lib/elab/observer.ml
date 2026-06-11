module Trie = Yuujinchou.Trie

type event =
  | Def of
      { path : Trie.path
      ; module_path : Trie.path
      ; loc : Asai.Range.t
      ; name_loc : Asai.Range.t option
      ; ty : Violet_kernel.Syntax.Core.value_ty
      ; pp_ty : string
      ; axiom_deps : Trie.path list
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

module H = Algaeff.Reader.Make (struct
    type t = event -> unit
  end)

let emit ev =
  let f = H.read () in
  f ev
;;

let run ~on_event f = H.run ~env:on_event f
let run_silent f = H.run ~env:(fun _ -> ()) f
