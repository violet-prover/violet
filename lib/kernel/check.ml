open Syntax
open Error

module Make (M : Views.META_VIEW) = struct
  (* A well-formedness check on a Core term.
     - All LocalVar indices must be in range of the given lvl.
     - Meta ids must be known to the meta store (via META_VIEW). *)
  let rec check_term (lvl : int) (t : Core.term) : unit =
    match t with
    | Core.Universe _ -> ()
    | Core.LocalVar ix ->
      if ix < 0 || ix >= lvl then raise (Kernel_error (UnboundLocal ix))
    | Core.Var _ -> ()
    | Core.App (a, b, _) ->
      check_term lvl a;
      check_term lvl b
    | Core.Lambda { bound; _ } -> check_term (lvl + 1) bound
    | Core.TypedLambda ({ bound; _ }, body) ->
      check_term lvl bound;
      check_term (lvl + 1) body
    | Core.Pi ({ bound; _ }, b) ->
      check_term lvl bound;
      check_term (lvl + 1) b
    | Core.Meta m | Core.InsertedMeta (m, _) ->
      (match M.lookup m with
       | Some _ -> ()
       | None when M.is_goal m -> ()
       | None -> raise (Kernel_error (OrphanMeta m)))
    | Core.Lift { ty; _ } -> check_term lvl ty
    | Core.LiftTerm { ty; tm; _ } | Core.UnliftTerm { ty; tm; _ } ->
      check_term lvl ty;
      check_term lvl tm
    | Core.RecordType { params; fields; _ } ->
      List.iter (check_term lvl) params;
      let rec walk lvl = function
        | [] -> ()
        | (b : Core.term Syntax.binder) :: rest ->
          check_term lvl b.bound;
          walk (lvl + 1) rest
      in
      walk lvl fields
    | Core.RecordIntro { fields; _ } -> List.iter (fun (_, t) -> check_term lvl t) fields
    | Core.RecordProj { record; _ } -> check_term lvl record
    | Core.IdAbsurd t -> check_term lvl t
    | Core.Empty -> ()
    | Core.Absurd t -> check_term lvl t
  ;;

  let accept_let m ~name ~ty ~body =
    check_term 0 ty;
    check_term 0 body;
    Module.declare m name (Module.Let { ty; body })
  ;;

  let accept_data m ~name ~ty ~ctor_names =
    check_term 0 ty;
    Module.declare m name (Module.Data { ty; ctor_names })
  ;;

  let accept_ctor m ~name ~data ~ty =
    check_term 0 ty;
    Module.declare m name (Module.Ctor { data; ty })
  ;;

  let accept_elim m ~name ~ty ~reducer =
    check_term 0 ty;
    Module.declare m name (Module.Elim { ty; reducer })
  ;;

  let accept_axiom m ~name ~ty =
    check_term 0 ty;
    Module.declare m name (Module.Axiom { ty })
  ;;
end
