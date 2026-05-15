open Syntax.Core
open Bwd
open Bwd.Infix

module Make (M : Views.META_VIEW) (E : Views.ENV_VIEW) = struct
  let rec vapp (t : value) (u : value) : value =
    match t with
    | VLambda { bound = f; _ } -> f u
    | Flex (m, sp) -> Flex (m, sp <: u)
    | RigidLocal (l, sp) -> RigidLocal (l, sp <: u)
    | Var (h, sp) -> Var (h, sp <: u)
    | Label (h, sp) -> Label (h, sp <: u)
    | IndType (h, sp) -> IndType (h, sp <: u)
    | Elim (h, sp) -> Elim (h, sp <: u)
    | v -> raise (Error.Kernel_error (Error.BadApplication v))

  and vapp_spine (t : value) : value bwd -> value = function
    | Emp -> t
    | Snoc (sp, u) -> vapp (vapp_spine t sp) u
  ;;

  let rec force : value -> value = function
    | Flex (m, sp) ->
      (match M.lookup m with
       | Some t -> force (vapp_spine t sp)
       | None -> Flex (m, sp))
    | t -> t
  ;;

  (* Like force but also unfolds opaque global heads.  Use when we need to see
     the WHNF spine of a value (e.g. for application type-checking, where the
     head must be a VPi).  Eliminators get a chance to ι-reduce: when an
     `Elim`'s target argument has reduced to a `Label`, its reducer fires;
     otherwise the head stays neutral. *)
  let rec force_head (v : value) : value =
    match force v with
    | Var (x, sp) ->
      (match E.unfold x with
       | Some def -> force_head (vapp_spine def sp)
       | None -> Var (x, sp))
    | Elim (({ reducer; _ } as h), sp) ->
      (match reducer sp with
       | Some reduced -> force_head reduced
       | None -> Elim (h, sp))
    | t -> t
  ;;

  (* env 是 value bwd，從外往內：最外層的 binder 在最左（Emp 那邊），
     最內層在最右（Snoc 那邊）。LocalVar 用 de Bruijn index：
     index 0 是最內層、index n 是從右數第 n+1 個。 *)
  let rec env_nth (env : value bwd) (i : int) : value =
    match env, i with
    | Snoc (_, v), 0 -> v
    | Snoc (rest, _), k -> env_nth rest (k - 1)
    | Emp, _ ->
      raise (Error.Kernel_error (Error.LocalVarOutOfRange { index = i; env_size = 0 }))
  ;;

  let rec eval (env : value bwd) (tm : term) : value =
    match tm with
    | Universe l -> Universe l
    | LocalVar i -> env_nth env i
    | Var x ->
      (match E.lookup x with
       | (Label _ | IndType _ | Elim _) as v -> v
       | _ -> Var (x, Emp))
    | App (t, u) -> vapp (eval env t) (eval env u)
    | Pi ({ name; bound; implicit }, b) ->
      VPi ({ name; bound = eval env bound; implicit }, fun v -> eval (env <: v) b)
    | Lambda { name; bound; implicit } ->
      VLambda { name; implicit; bound = (fun v -> eval (env <: v) bound) }
    | TypedLambda ({ name; implicit; _ }, body) ->
      VLambda { name; implicit; bound = (fun v -> eval (env <: v) body) }
    | Meta m -> M.eval m
    | InsertedMeta (m, n) -> vapp_locals (M.eval m) env n
    | Lift { from_lvl; to_lvl; ty } -> VLift { from_lvl; to_lvl; ty = eval env ty }
    | LiftTerm { from_lvl; to_lvl; ty; tm } ->
      let v_ty = eval env ty in
      let v_tm = eval env tm in
      (match v_tm with
       | VUnliftTerm inner
         when Level.equal inner.from_lvl from_lvl && Level.equal inner.to_lvl to_lvl ->
         inner.tm
       | _ -> VLiftTerm { from_lvl; to_lvl; ty = v_ty; tm = v_tm })
    | UnliftTerm { from_lvl; to_lvl; ty; tm } ->
      let v_ty = eval env ty in
      let v_tm = eval env tm in
      (match v_tm with
       | VLiftTerm inner
         when Level.equal inner.from_lvl from_lvl && Level.equal inner.to_lvl to_lvl ->
         inner.tm
       | _ -> VUnliftTerm { from_lvl; to_lvl; ty = v_ty; tm = v_tm })

  (* 把 v 套上 env 的 outermost n 個 local。env 從外往內，
     所以 outermost 是 env 從左數起的 n 個元素。 *)
  and vapp_locals (v : value) (env : value bwd) (n : int) : value =
    let env_size = Bwd.length env in
    if n > env_size
    then raise (Error.Kernel_error (Error.LocalVarOutOfRange { index = n; env_size }))
    else begin
      (* env_nth_from_left env k = env 從左數第 k 個 *)
      let rec env_nth_from_left env k =
        match env with
        | Emp ->
          raise
            (Error.Kernel_error (Error.LocalVarOutOfRange { index = k; env_size = 0 }))
        | Snoc (rest, top) ->
          let depth = Bwd.length env in
          if depth = k + 1 then top else env_nth_from_left rest k
      in
      let rec apply i acc =
        if i = n then acc else apply (i + 1) (vapp acc (env_nth_from_left env i))
      in
      apply 0 v
    end
  ;;
end

(* Trivial no-op views used only for the expect-tests below.
   Metas are always unknown; env lookups always return a free variable. *)
module NullMeta : Views.META_VIEW = struct
  let lookup _ = None
  let eval m = Flex (m, Emp)
  let is_goal _ = false
end

module NullEnv : Views.ENV_VIEW = struct
  let lookup x = Var (x, Emp)
  let unfold _ = None
end

module Test = Make (NullMeta) (NullEnv)

let%expect_test "eval Universe" =
  print_string @@ [%show: value] (Test.eval Emp (Universe Level.LZero));
  [%expect {| 𝓤 |}]
;;

let%expect_test "lift unlift cancels" =
  let zero = Level.lzero in
  let one = Level.lsuc Level.lzero in
  (* env contains a single value `x` (printed as `$0`) at de Bruijn index 0.
     `Var "A"` is also stored as a value so eval doesn't hit Env.lookup. *)
  let x_val = rigid_local 0 in
  let a_val = rigid_local 1 in
  let env = Bwd.Infix.(Bwd.Emp <: a_val <: x_val) in
  let v =
    Test.eval
      env
      (LiftTerm
         { from_lvl = zero
         ; to_lvl = one
         ; ty = LocalVar 1
         ; tm =
             UnliftTerm
               { from_lvl = zero; to_lvl = one; ty = LocalVar 1; tm = LocalVar 0 }
         })
  in
  print_string @@ [%show: value] v;
  [%expect {| $0 |}]
;;
