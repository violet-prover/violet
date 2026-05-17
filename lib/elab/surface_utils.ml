(* Small Surface-AST helpers shared between core elaboration (elab.ml) and
   the inductive/elim subset (inductive.ml). *)

(* Best location for a Surface preterm — peels through `Located` wrappers to
   find the innermost recorded range. Returns `None` when no wrapper is
   present (e.g. for terms synthesized by the elaborator). *)
let rec loc_of : Surface.preterm -> Asai.Range.t option = function
  | Surface.Located { loc; value } ->
    (match loc_of value with
     | Some _ as inner -> inner
     | None -> loc)
  | _ -> None
;;

(* Peel `n` outer Pi-layers off a Surface pretype, returning the codomain. *)
let rec peel_pi_surface ~(loc : Asai.Range.t) (n : int) (s : Surface.pretype)
  : Surface.pretype
  =
  if n = 0
  then s
  else (
    match s with
    | Surface.Located { value; loc = inner } ->
      peel_pi_surface ~loc:(Option.value inner ~default:loc) n value
    | Surface.Pi (_, cod) -> peel_pi_surface ~loc (n - 1) cod
    | _ ->
      Reporter.fatalf
        ~loc
        Elab_error
        "stack-def: signature has fewer Pi-layers than required (%d remaining)"
        n)
;;
