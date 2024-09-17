open Syntax.Core
open Bwd
open Bwd.Infix

let rec vapp (t : value) (u : value) : value =
  match t with
  | VLambda f -> f u
  | Flex (m, t) -> Flex (m, t <: u)
  | Rigid (h, t) -> Rigid (h, t <: u)
  | v -> Reporter.fatalf Elab_error "cannot apply on %s" ([%show: value] v)

and vapp_spine (t : value) : value bwd -> value = function
  | Emp -> t
  | Snoc (sp, u) -> vapp (vapp_spine t sp) u

let meta_context = Hashtbl.create ~random:true 100

let lookup_meta (mvar : metavar) : value option =
  Hashtbl.find_opt meta_context mvar

let insert_meta (mvar : metavar) (solution : value) : unit =
  Hashtbl.add meta_context mvar solution

let eval_meta (mvar : metavar) : value =
  match lookup_meta mvar with Some t -> t | None -> Flex (mvar, Emp)

let rec force : value -> value = function
  | Flex (m, sp) -> (
      match lookup_meta m with
      | Some t -> force (vapp_spine t sp)
      | None -> Flex (m, sp))
  | t -> t

let rec eval (tm : term) : value =
  match tm with
  | Universe -> Universe
  | Var x -> Env.lookup x
  | App (t, u) ->
      let t = eval t in
      let u = eval u in
      vapp t u
  | Pi ({ name; bound; implicit }, b) ->
      VPi
        ( { name; bound = eval bound; implicit },
          fun v ->
            Env.S.section [] @@ fun () ->
            Env.S.include_singleton ([ name ], (v, `Local));
            eval b )
  | Lambda { name; bound; implicit = _ } ->
      VLambda
        (fun v ->
          Env.S.section [] @@ fun () ->
          Env.S.include_singleton ([ name ], (v, `Local));
          eval bound)
  | Meta m -> eval_meta m
  | InsertedMeta (m, bounds) -> vapp_bounds (eval_meta m) bounds
and vapp_bounds (v : value) (bounds : string bwd) =
  match bounds with
  | Emp -> v
  | Snoc (bounds, x) -> vapp (vapp_bounds v bounds) (eval (Var x))
