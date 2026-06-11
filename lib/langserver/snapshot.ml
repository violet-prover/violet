module Trie = Yuujinchou.Trie

type t =
  { module_path : Trie.path
  ; diagnostics : Linol_lsp.Lsp.Types.Diagnostic.t list
  ; index : Violet_interactive.Index.t
  ; last_good_index : Violet_interactive.Index.t
  }

let empty ~module_path =
  { module_path
  ; diagnostics = []
  ; index = Violet_interactive.Index.empty
  ; last_good_index = Violet_interactive.Index.empty
  }
;;
