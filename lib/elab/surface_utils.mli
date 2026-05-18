(* Small Surface-AST helpers shared between core elaboration (elab.ml) and
   the inductive/elim subset (inductive.ml). *)

open Violet_kernel.Syntax

(* Best location for a Surface preterm — peels through `Located` wrappers to
   find the innermost recorded range. Returns `None` when no wrapper is
   present (e.g. for terms synthesized by the elaborator). *)
val loc_of : Surface.preterm -> Asai.Range.t option

(* Peel `n` outer Pi-layers off a Surface pretype, returning the codomain. *)
val peel_pi_surface : loc:Asai.Range.t -> int -> Surface.pretype -> Surface.pretype

(* Linearize a chain of leading Pi-types into its binders plus final codomain.
   Walks through [Located] wrappers. For [t = Pi b1 (Pi b2 ... (Pi bn cod))]
   returns [([b1; ...; bn], cod)]; if [t] starts with a non-Pi the list is
   empty and [cod = t]. *)
val linearize_pi : Surface.pretype -> Surface.pretype binder list * Surface.pretype

(* The Pi-domain binders of [t] — the first projection of [linearize_pi]. *)
val pi_domain : Surface.pretype -> Surface.pretype binder list

(* The head of a Surface preterm — i.e. the term you get by stripping all
   applications (and `Located` wrappers) on the left. *)
val head_of_surface : Surface.preterm -> Surface.preterm

(* Does the global name `target` occur (as a Surface.Var) anywhere in `t`,
   respecting shadowing by inner binders that re-bind the same name? *)
val occurs_in : string -> Surface.preterm -> bool

(* Split a term into its head and applied spine (in left-to-right order). *)
val head_and_spine : Surface.preterm -> Surface.preterm * Surface.preterm list

(* Map every free single-segment `Var [n]` occurrence in a Surface preterm.
   The traversal is binder-aware: `enter name scope` extends the scope before
   descending into the body/codomain of Lambda/TypedLambda/Pi (the domain of
   TypedLambda/Pi is walked under the outer scope). Multi-segment names
   `Var [a; b; ...]` are left untouched. Op_soup is treated as an internal
   error (the resolver should have lowered it). *)
val map_free_vars
  :  on_var:('s -> string -> Surface.preterm)
  -> enter:(string -> 's -> 's)
  -> 's
  -> Surface.preterm
  -> Surface.preterm
