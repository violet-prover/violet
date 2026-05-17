(* Small Surface-AST helpers shared between core elaboration (elab.ml) and
   the inductive/elim subset (inductive.ml). *)

(* Best location for a Surface preterm — peels through `Located` wrappers to
   find the innermost recorded range. Returns `None` when no wrapper is
   present (e.g. for terms synthesized by the elaborator). *)
val loc_of : Surface.preterm -> Asai.Range.t option

(* Peel `n` outer Pi-layers off a Surface pretype, returning the codomain. *)
val peel_pi_surface : loc:Asai.Range.t -> int -> Surface.pretype -> Surface.pretype
