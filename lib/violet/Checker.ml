open Syntax
open Bwd
open Evaluation

(* local_ctx tracks:
   - env:   values for de Bruijn indexing during eval
   - types: types of the same locals, for type-checking lookup
   - names: surface names of the same locals, for surface→core resolution
   - lvl:   current de Bruijn level (= Bwd.length env), threaded for fresh metas
   All four grow together — `extend` keeps them in sync. *)
type local_ctx =
  { env : Core.value bwd
  ; types : Core.value bwd
  ; names : string bwd
  ; lvl : int
  }

let empty_ctx : local_ctx = { env = Emp; types = Emp; names = Emp; lvl = 0 }

let extend (ctx : local_ctx) (name : string) (ty : Core.value) (value : Core.value)
  : local_ctx
  =
  { env = Bwd.Snoc (ctx.env, value)
  ; types = Bwd.Snoc (ctx.types, ty)
  ; names = Bwd.Snoc (ctx.names, name)
  ; lvl = ctx.lvl + 1
  }
;;

(* `bind` is the common case: pushing a new binder.  The value placeholder is
   a fresh RigidLocal at the current level. *)
let bind (ctx : local_ctx) (name : string) (ty : Core.value) : local_ctx =
  extend ctx name ty (Core.RigidLocal (ctx.lvl, Emp))
;;

(* Look up a surface name in the local context.  Returns the de Bruijn INDEX
   (innermost = 0) if found, or None if it's a global. *)
let resolve_local (ctx : local_ctx) (x : string) : int option =
  let rec go i = function
    | Emp -> None
    | Snoc (rest, n) -> if String.equal n x then Some i else go (i + 1) rest
  in
  go 0 ctx.names
;;

(* Look up the type of a local by index, mirroring resolve_local. *)
let local_type (ctx : local_ctx) (ix : int) : Core.value =
  let rec nth env i =
    match env, i with
    | Snoc (_, v), 0 -> v
    | Snoc (rest, _), k -> nth rest (k - 1)
    | Emp, _ -> Reporter.fatalf Elab_error "local index %d out of range in types" ix
  in
  nth ctx.types ix
;;

let rec check ~loc (ctx : local_ctx) (term : Surface.preterm) (typ : Core.value_ty)
  : Core.term
  =
  match term, typ with
  | Surface.Located { loc; value }, _ -> check ~loc:(Option.get loc) ctx value typ
  | ( Lambda { name = x; bound = body; implicit = lambda_mode }
    , VPi ({ name = _; bound = a; implicit = pi_mode }, b) ) ->
    if lambda_mode != pi_mode
    then Reporter.fatalf ~loc Elab_error "mode mismatching"
    else (
      let ctx' = bind ctx x a in
      let body = check ~loc ctx' body (b (Core.RigidLocal (ctx.lvl, Emp))) in
      Core.Lambda { name = x; bound = body; implicit = lambda_mode })
  | Hole, _ -> Meta.meta_fresh ctx.lvl
  | tm, expected_typ ->
    let tm, infer_typ = infer ~loc ctx tm in
    Eio.traceln
      "checking `%s` has type `%s ~ %s`\n"
      ([%show: Core.term] tm)
      ([%show: Core.value] expected_typ)
      ([%show: Core.value] infer_typ);
    Unification.unify ~loc ctx.lvl expected_typ infer_typ;
    tm

and infer ~loc (ctx : local_ctx) : Surface.preterm -> Core.term * Core.value_ty = function
  | Located { loc; value } -> infer ~loc:(Option.get loc) ctx value
  | Universe -> Universe, Universe
  | Var x ->
    (match resolve_local ctx x with
     | Some i -> Core.LocalVar i, local_type ctx i
     | None -> Core.Var x, Context.lookup x)
  | Pi ({ name; bound = a; implicit }, b) ->
    let a = check ~loc ctx a Universe in
    let a_val = eval ctx.env a in
    let ctx' = bind ctx name a_val in
    let b = check ~loc ctx' b Universe in
    Core.Pi ({ name; bound = a; implicit }, b), Core.Universe
  | App (is_implicit, f, arg) ->
    let f', f_typ = infer ~loc ctx f in
    (* Unfold opaque global heads (e.g. `motive x` -> `Nat -> Nat`) so an
       application type-check can see a VPi. *)
    (match force_head f_typ with
     | VPi ({ implicit; name = _; bound = a }, b) ->
       if is_implicit == implicit
       then begin
         let arg' = check ~loc ctx arg a in
         App (f', arg'), b @@ eval ctx.env arg'
       end
       else if implicit
       then begin
         infer ~loc ctx @@ App (false, App (implicit, f, Hole), arg)
       end
       else begin
         Reporter.fatalf
           ~loc
           Elab_error
           "Bad apply %s %s"
           ([%show: Surface.preterm] f)
           ([%show: Surface.preterm] arg)
       end
     | ty ->
       Reporter.fatalf
         ~loc
         Type_error
         "cannot apply a value `%s` to `(%s) : %s`"
         ([%show: Surface.preterm] arg)
         ([%show: Core.term] f')
         ([%show: Core.value_ty] ty))
  | Hole ->
    let ty = eval ctx.env @@ Meta.meta_fresh ctx.lvl in
    let t = Meta.meta_fresh ctx.lvl in
    t, ty
  | TypedLambda ({ name; bound = ty; implicit }, body) ->
    let ty = check_type ~loc ctx ty in
    let ty_val = eval ctx.env ty in
    let ctx' = bind ctx name ty_val in
    let body, ty_of_body = infer ~loc ctx' body in
    ( Core.TypedLambda ({ name; bound = ty; implicit }, body)
    , Core.VPi ({ name; bound = ty_val; implicit }, fun _ -> ty_of_body) )
  | Lambda _ -> Reporter.fatalf ~loc Elab_error "cannot infer lambda term"

and check_type ~loc (ctx : local_ctx) (pretype : Surface.pretype) : Core.term =
  check ~loc ctx pretype Universe
;;

(* Wrap a constructor's user-written type with implicit Π over the inductive
   type's params, so the stored global type is self-contained and so the
   params are in scope while checking the user's constructor type.

   `data List (A : U) : U | nil : List A`
   stores nil : Π{A : U} -> List A

   Params are always wrapped — they're shared with the data declaration, so
   the user should never re-introduce them. Deps are not auto-wrapped: ctors
   that constrain a dep (like `nil : Vec A zero` pinning n=zero) shouldn't
   take an n binder. *)
let close_ctor_type (params : Surface.pretype binder list) (typ : Surface.pretype)
  : Surface.pretype
  =
  List.fold_right
    (fun param result -> Surface.Pi ({ param with implicit = true }, result))
    params
    typ
;;

let bind_constructor
      ~loc
      (ctx : local_ctx)
      (params : Surface.pretype binder list)
      ({ name; bound = typ; _ } : Surface.pretype binder)
  : unit
  =
  let typ = close_ctor_type params typ in
  let ctor_ty_tm = check ~loc ctx typ Universe in
  let ctor_ty = eval ctx.env ctor_ty_tm in
  Context.S.include_singleton ([ name ], (ctor_ty, `Constructor));
  Env.S.include_singleton ([ name ], (Label (name, Bwd.Emp), `Constructor))
;;

let bind_of_case
      ~loc
      (ctx : local_ctx)
      ind_name
      motive_name
      ({ name; bound = typ; _ } : Surface.pretype binder)
  : Surface.pretype binder
  =
  let tele = Surface.telescope typ in
  let counter = ref (-1) in
  let tele =
    List.map
      (fun bind ->
         incr counter;
         { bind with
           name = (if bind.name = "_" then "x" ^ string_of_int !counter else bind.name)
         })
      tele
  in
  let recursive_points =
    List.filter
      (fun bind ->
         let typ = bind.bound in
         let typ = check_type ~loc ctx typ in
         let typ = eval ctx.env typ in
         match typ with
         | IndType (head, _) -> head == ind_name
         | _ -> false)
      tele
  in
  let motives =
    List.map
      (fun { name; _ } ->
         { name = "fix"
         ; bound = Surface.apply (Var motive_name) [ Var name ]
         ; implicit = false
         })
      recursive_points
  in
  { name = "case-" ^ name
  ; bound =
      List.fold_right
        (fun bind result -> Surface.Pi (bind, result))
        (List.append tele motives)
        (Surface.apply
           (Var motive_name)
           [ (if List.is_empty tele then Var name else Surface.apply_tele (Var name) tele)
           ])
  ; implicit = false
  }
;;

let rec check_module (file : Surface.t) : unit =
  let module_name = Filename.chop_extension @@ Filename.basename file.name in
  Eio.traceln "checking [module] %s (%s)" module_name file.name;
  Context.S.section [ module_name ]
  @@ fun () ->
  Env.S.section [ module_name ]
  @@ fun () ->
  List.iter
    (fun library ->
       (Context.S.modify_visible
        @@ Yuujinchou.Language.(union [ all; renaming library [] ]));
       Env.S.modify_visible @@ Yuujinchou.Language.(union [ all; renaming library [] ]))
    file.imports;
  List.iter
    (fun (top : Surface.top Asai.Range.located) ->
       let loc = Option.get top.loc in
       check_top ~loc top.value)
    file.tops

and check_top ~loc top =
  let ctx = empty_ctx in
  match top with
  | Surface.Data { name; params; deps; ind_ty; ctors } ->
    handle_inductive_type ~loc ctx name params deps ind_ty ctors
  | Surface.Let (name, bindings, result_ty, body) ->
    let typ : Surface.pretype =
      List.fold_right
        (fun binding return_ty -> Surface.Pi (binding, return_ty))
        bindings
        result_ty
    in
    Reporter.tracef ~loc "checking [top let] %s : %s" name ([%show: Surface.pretype] typ)
    @@ fun () ->
    let typ_tm = check_type ~loc ctx typ in
    let typ_val = eval ctx.env typ_tm in
    let term : Surface.preterm =
      List.fold_right
        (fun { name; implicit; bound = _ } body ->
           Surface.Lambda { name; bound = body; implicit })
        bindings
        body
    in
    let term = check ~loc ctx term typ_val in
    Context.S.include_singleton
      ~context_visible:`Visible
      ~context_export:`Export
      ([ name ], (typ_val, `Constructor));
    let body_val = eval ctx.env term in
    Env.S.include_singleton
      ~context_visible:`Visible
      ~context_export:`Export
      ([ name ], (body_val, `Constructor));
    Env.register_definition name body_val

and handle_inductive_type
      ~loc
      (ctx : local_ctx)
      name_of_the_inductive_type
      params
      deps
      ind_ty
      ctors
  =
  let _ = deps in
  Reporter.tracef ~loc "checking [inductive data type] %s" name_of_the_inductive_type
  @@ fun () ->
  let typ : Surface.pretype =
    List.fold_right
      (fun binding return_ty -> Surface.Pi (binding, return_ty))
      (params @ deps)
      ind_ty
  in
  let typ_tm = check_type ~loc ctx typ in
  let typ_val = eval ctx.env typ_tm in
  Context.S.include_singleton
    ~context_visible:`Visible
    ~context_export:`Export
    ([ name_of_the_inductive_type ], (typ_val, `Constructor));
  Env.S.include_singleton
    ~context_visible:`Visible
    ~context_export:`Export
    ( [ name_of_the_inductive_type ]
    , (IndType (name_of_the_inductive_type, Bwd.Emp), `Constructor) );
  List.iter (bind_constructor ~loc ctx params) ctors;
  let typ : Surface.pretype =
    ElabData.eliminator_type ~name:name_of_the_inductive_type ~params ~deps ~ind_ty ctors
  in
  let eliminator_name = name_of_the_inductive_type ^ "-elim" in
  Eio.traceln "ELIMINATOR %s : %s\n" eliminator_name ([%show: Surface.pretype] typ);
  let typ_tm = check ~loc ctx typ Universe in
  let typ_val = eval ctx.env typ_tm in
  Context.S.include_singleton
    ~context_visible:`Visible
    ~context_export:`Export
    ([ eliminator_name ], (typ_val, `Constructor));
  let reducer =
    ElabData.build_elim_reducer
      ~ind_name:name_of_the_inductive_type
      ~elim_name:eliminator_name
      ~params
      ~deps
      ctors
  in
  let elim_value = Core.Elim ({ elim_name = eliminator_name; reducer }, Bwd.Emp) in
  Env.S.include_singleton
    ~context_visible:`Visible
    ~context_export:`Export
    ([ eliminator_name ], (elim_value, `Constructor))
;;
