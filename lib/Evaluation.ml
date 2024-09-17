open Syntax
open Bwd
open Bwd.Infix

exception TODO

let vapp (t : Core.value) (u : Core.value) : Core.value =
  match t with
  | VLambda f -> f u
  | Flex (m, t) -> Flex (m, t <: u)
  | Rigid (h, t) -> Rigid (h, t <: u)
  | v -> Reporter.fatalf Elab_error "cannot apply on %s" ([%show: Core.value] v)

let rec eval (tm : Core.term) : Core.value =
  match tm with
  | Universe -> Universe
  | Var x -> Env.lookup x
  | App (t, u) ->
      let t = eval t in
      let u = eval u in
      vapp t u
  | Pi ({ name; bound; implicit }, b) ->
      Core.VPi
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
  | Meta m -> Meta.eval m
  | InsertedMeta _ -> raise TODO
