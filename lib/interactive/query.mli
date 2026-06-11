module Trie = Yuujinchou.Trie

type definition_result =
  { path : Trie.path
  ; loc : Asai.Range.t
  }

type reference =
  { loc : Asai.Range.t
  ; kind : Index.entry_kind
  }

val goto_definition
  :  source:string
  -> line:int
  -> col:int
  -> Index.t
  -> definition_result option

val find_references : source:string -> line:int -> col:int -> Index.t -> reference list
