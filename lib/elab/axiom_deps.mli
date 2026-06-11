(* Per-name tracking of which axioms a top-level definition transitively
   depends on. Process-global, mirroring [Env.definitions]. A name's identity
   is its complete Yuujinchou id ([Trie.path]) — the same representation
   [Observer.Def.path] carries — not a bare string. *)

module Syntax = Violet_kernel.Syntax
module Trie = Yuujinchou.Trie

(* Mark [p] as an axiom: it depends on itself. *)
val register_axiom : Trie.path -> unit

(* Record that [p]'s type/body reference [refs]; stores the union of each
   ref's axiom set. Call AFTER the refs are already registered (guaranteed by
   source-order, no-forward-reference elaboration). *)
val register_def : Trie.path -> refs:Trie.path list -> unit

(* The sorted, de-duplicated set of axioms [p] transitively depends on.
   Empty for unknown ids. Includes [p] itself iff [p] is an axiom. *)
val deps_of : Trie.path -> Trie.path list

(* [deps_of p] with [p] itself removed — the form shown to users (hover,
   REPL, goal reports, Def events). *)
val display_deps_of : Trie.path -> Trie.path list

(* Every global [Core.Var] head occurring anywhere in [t], each as its
   complete id (the head's "/"-joined form split back into a path). *)
val refs_in_term : Syntax.Core.term -> Trie.path list

(* Clear the registry. For test isolation. *)
val reset : unit -> unit
