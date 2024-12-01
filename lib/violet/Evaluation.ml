open Syntax.Core
open Bwd
open Bwd.Infix

let rec vapp (t : value) (u : value) : value =
  match t with
  | VLambda { bound = f; _ } -> f u
  | Flex (m, t) -> Flex (m, t <: u)
  | Rigid (h, t) -> Rigid (h, t <: u)
  | v -> Reporter.fatalf Elab_error "cannot apply on %s" ([%show: value] v)

and vapp_spine (t : value) : value bwd -> value = function
  | Emp -> t
  | Snoc (sp, u) -> vapp (vapp_spine t sp) u
;;

let rec force : value -> value = function
  | Flex (m, sp) ->
    (match Meta.lookup_meta m with
     | Some t -> force (vapp_spine t sp)
     | None -> Flex (m, sp))
  | t -> t
;;

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
      ( { name; bound = eval bound; implicit }
      , fun v ->
          Env.S.section []
          @@ fun () ->
          Env.S.include_singleton ([ name ], (v, `Local));
          eval b )
  | Lambda { name; bound; implicit } ->
    VLambda
      { name
      ; implicit
      ; bound =
          (fun v ->
            Env.S.section []
            @@ fun () ->
            Env.S.include_singleton ([ name ], (v, `Local));
            eval bound)
      }
  | Meta m -> Meta.eval m
  | InsertedMeta (m, bounds) -> vapp_bounds (Meta.eval m) bounds

and vapp_bounds (v : value) (bounds : string bwd) =
  match bounds with
  | Emp -> v
  | Snoc (bounds, x) -> vapp (vapp_bounds v bounds) (eval (Var x))
;;
