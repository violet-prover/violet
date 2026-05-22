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

  and vrecord_proj (v : value) (f : string) : value =
    match v with
    | VRecordIntro r ->
      (try List.assoc f r.fields with
       | Not_found ->
         raise (Error.Kernel_error (Error.BadProjection { value = v; field = f })))
    | Flex _ | RigidLocal _ | Var _ | Label _ | IndType _ | Elim _ | VRecordProj _ ->
      VRecordProj (v, f)
    | _ -> raise (Error.Kernel_error (Error.BadProjection { value = v; field = f }))
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
    | VRecordProj (inner, f) ->
      (match force_head inner with
       | VRecordIntro r as full ->
         (try force_head (List.assoc f r.fields) with
          | Not_found ->
            raise (Error.Kernel_error (Error.BadProjection { value = full; field = f })))
       | other -> VRecordProj (other, f))
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
    | RecordType { name; params; fields } ->
      let v_params = List.map (eval env) params in
      let rec walk env_extended = function
        | [] -> []
        | (b : typ Syntax.binder) :: rest ->
          let b_val = eval env_extended b.bound in
          let head_lvl = Bwd.length env_extended in
          { b with bound = b_val } :: walk (env_extended <: rigid_local head_lvl) rest
      in
      let v_fields = walk env fields in
      VRecordType
        { name
        ; params = v_params
        ; fields = v_fields
        ; field_env = env
        ; field_terms = fields
        }
    | RecordIntro { name; fields } ->
      VRecordIntro { name; fields = List.map (fun (f, t) -> f, eval env t) fields }
    | RecordProj { record; field } ->
      let v = eval env record in
      vrecord_proj v field
    | IdAbsurd t -> VIdAbsurd (eval env t)

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
  [%expect {| universe 𝓤₀ |}]
;;

let%expect_test "lift unlift cancels" =
  let zero = Level.lzero in
  let one = Level.lsuc Level.lzero in
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

let%expect_test "eval RecordType with no params and flat fields" =
  let ty : term =
    RecordType
      { name = "Point"
      ; params = []
      ; fields =
          [ { name = Named "x"; bound = Var "Nat"; implicit = false }
          ; { name = Named "y"; bound = Var "Nat"; implicit = false }
          ]
      }
  in
  let v = Test.eval Bwd.Emp ty in
  print_string @@ [%show: value] v;
  [%expect {| (record Point | x : Nat | y : Nat) |}]
;;

let%expect_test "eval RecordIntro" =
  let tm : term =
    RecordIntro { name = "Point"; fields = [ "x", Var "zero"; "y", Var "one" ] }
  in
  let v = Test.eval Bwd.Emp tm in
  print_string @@ [%show: value] v;
  [%expect {| Point{ x = zero, y = one } |}]
;;

let%expect_test "RecordProj on RecordIntro reduces" =
  let tm : term =
    RecordProj
      { record = RecordIntro { name = "Point"; fields = [ "x", Universe Level.LZero ] }
      ; field = "x"
      }
  in
  print_string @@ [%show: value] (Test.eval Bwd.Emp tm);
  [%expect {| universe 𝓤₀ |}]
;;

let%expect_test "RecordProj on neutral stays neutral" =
  let tm : term = RecordProj { record = Var "p"; field = "x" } in
  print_string @@ [%show: value] (Test.eval Bwd.Emp tm);
  [%expect {| p.x |}]
;;

let%expect_test "eval RecordType with dependent fields uses rigid locals" =
  (* Sigma A B-style: fst : A, snd : B fst.
     With env Emp:
       - param "B" appears as a Var "B" applied to LocalVar 0 (= fst, which has level 0)
       - after evaluating field 0 (= "fst" of type Var "A"), env_extended is < $0 >
       - eval of "B fst" (= "App (Var B, LocalVar 0)") in env_extended produces:
         vapp (Var "B" with empty spine) (RigidLocal 0 Emp) → Var ("B", [RigidLocal 0 Emp]) *)
  let ty : term =
    RecordType
      { name = "Sigma"
      ; params = [ Var "A"; Var "B" ]
      ; fields =
          [ { name = Named "fst"; bound = Var "A"; implicit = false }
          ; { name = Named "snd"; bound = App (Var "B", LocalVar 0); implicit = false }
          ]
      }
  in
  let v = Test.eval Bwd.Emp ty in
  print_string @@ [%show: value] v;
  [%expect {| (record Sigma A B | fst : A | snd : B $0) |}]
;;
