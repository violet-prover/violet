open Syntax
open Bwd

let pp_local_name (cv : Context_view.t) (lvl : int) : string =
  match Context_view.nth_name_from_lvl cv lvl with
  | Some n -> n
  | None -> Printf.sprintf "$%d" lvl
;;

let rec pp_level_atom (l : Level.level) : string =
  match Level.force_level l with
  | Level.LZero -> "0"
  | Level.LVar v -> v
  | Level.LMeta i -> Printf.sprintf "?lvl%d" i
  | Level.LSuc _ | Level.LMax _ -> "(" ^ pp_level l ^ ")"

and pp_level (l : Level.level) : string =
  match Level.force_level l with
  | Level.LZero -> "0"
  | Level.LVar v -> v
  | Level.LMeta i -> Printf.sprintf "?lvl%d" i
  | Level.LSuc l' -> "S " ^ pp_level_atom l'
  | Level.LMax (a, b) -> pp_level_atom a ^ " ⊔ " ^ pp_level_atom b
;;

let pp_universe (l : Level.level) : string =
  match l with
  | Level.LZero -> "universe 𝓤₀"
  | _ -> "universe " ^ pp_level l
;;

let pp_metavar (Core.MetaVar i : Core.metavar) : string = Printf.sprintf "?%d" i

let rec pp_value (cv : Context_view.t) (v : Core.value) : string =
  match v with
  | Core.Universe l -> pp_universe l
  | Core.RigidLocal (lvl, spine) -> pp_neutral cv (pp_local_name cv lvl) spine
  | Core.Var (n, spine) -> pp_neutral cv n spine
  | Core.IndType (n, spine) -> pp_neutral cv n spine
  | Core.Label (n, spine) -> pp_neutral cv n spine
  | Core.Flex (m, spine) -> pp_neutral cv (pp_metavar m) spine
  | Core.Elim ({ elim_name; _ }, spine) -> pp_neutral cv elim_name spine
  | Core.VPi ({ name; bound; implicit }, closure) ->
    let body = closure (Core.RigidLocal (Context_view.lvl cv, Emp)) in
    let ns = Name.to_string name in
    let cv' = Context_view.extend cv ns in
    let l, r = if implicit then "{", "}" else "(", ")" in
    Printf.sprintf "%s%s : %s%s -> %s" l ns (pp_value cv bound) r (pp_value cv' body)
  | Core.VLambda { name; bound = closure; implicit } ->
    let body = closure (Core.RigidLocal (Context_view.lvl cv, Emp)) in
    let ns = Name.to_string name in
    let cv' = Context_view.extend cv ns in
    if implicit
    then Printf.sprintf "(fun {%s} => %s)" ns (pp_value cv' body)
    else Printf.sprintf "(fun %s => %s)" ns (pp_value cv' body)
  | Core.VLift { from_lvl; to_lvl; ty } ->
    Printf.sprintf "lift[%s→%s] %s" (pp_level from_lvl) (pp_level to_lvl) (pp_value cv ty)
  | Core.VLiftTerm { from_lvl; to_lvl; ty; tm } ->
    Printf.sprintf
      "liftₜ[%s→%s] (%s : %s)"
      (pp_level from_lvl)
      (pp_level to_lvl)
      (pp_value cv tm)
      (pp_value cv ty)
  | Core.VUnliftTerm { from_lvl; to_lvl; ty; tm } ->
    Printf.sprintf
      "unliftₜ[%s→%s] (%s : %s)"
      (pp_level from_lvl)
      (pp_level to_lvl)
      (pp_value cv tm)
      (pp_value cv ty)
  | Core.VRecordType { name; params; fields; _ } ->
    let p_params = List.map (pp_value cv) params in
    let rec walk cv = function
      | [] -> []
      | (b : Core.value_ty Syntax.binder) :: rest ->
        let t_str = pp_value cv b.bound in
        let bs = Name.to_string b.name in
        let cv' = Context_view.extend cv bs in
        (bs ^ " : " ^ t_str) :: walk cv' rest
    in
    let field_strs = walk cv fields in
    let p =
      match p_params with
      | [] -> ""
      | _ -> " " ^ String.concat " " p_params
    in
    let fs = String.concat " " (List.map (fun s -> "| " ^ s) field_strs) in
    Printf.sprintf "(record %s%s %s)" name p fs
  | Core.VRecordIntro { name; fields } ->
    let fs =
      String.concat ", " (List.map (fun (f, v) -> f ^ " = " ^ pp_value cv v) fields)
    in
    Printf.sprintf "%s{ %s }" name fs
  | Core.VRecordProj (v, f, sp) ->
    pp_neutral cv (Printf.sprintf "%s.%s" (pp_value cv v) f) sp
  | Core.VIdAbsurd v -> Printf.sprintf "id-absurd %s" (pp_value cv v)
  | Core.VEmpty -> "Empty"
  | Core.VAbsurd (s, sp) -> pp_neutral cv (Printf.sprintf "absurd %s" (pp_value cv s)) sp

and pp_neutral (cv : Context_view.t) (head : string) (spine : Core.spine) : string =
  (* implicit arguments 隱藏的目的是讓 goal target 可閱讀 *)
  let explicit = List.filter (fun (a : Core.arg) -> not a.implicit) (Bwd.to_list spine) in
  match explicit with
  | [] -> head
  | args ->
    head ^ " " ^ String.concat " " (List.map (fun (a : Core.arg) -> pp_arg cv a.tm) args)

and pp_arg (cv : Context_view.t) (v : Core.value) : string =
  match v with
  | Core.Universe _
  | Core.RigidLocal (_, Emp)
  | Core.Var (_, Emp)
  | Core.IndType (_, Emp)
  | Core.Label (_, Emp)
  | Core.Flex (_, Emp) -> pp_value cv v
  | _ -> "(" ^ pp_value cv v ^ ")"
;;

let rec pp_term (cv : Context_view.t) (t : Core.term) : string =
  match t with
  | Core.Universe l -> pp_universe l
  | Core.LocalVar ix ->
    let lvl = Context_view.lvl cv - 1 - ix in
    (match Context_view.nth_name_from_lvl cv lvl with
     | Some n -> n
     | None -> Printf.sprintf "$%d" ix)
  | Core.Var n -> n
  | Core.App _ ->
    let rec collect t acc =
      match t with
      | Core.App (f, a, implicit) -> collect f ((a, implicit) :: acc)
      | _ -> t, acc
    in
    let head, args = collect t [] in
    (* implicit arguments 隱藏的目的是讓 goal target 可閱讀 *)
    let explicit = List.filter (fun (_, implicit) -> not implicit) args in
    (match explicit with
     | [] -> pp_term cv head
     | _ ->
       pp_term cv head
       ^ " "
       ^ String.concat " " (List.map (fun (a, _) -> pp_term_arg cv a) explicit))
  | Core.Lambda { name; bound; implicit } ->
    let ns = Name.to_string name in
    let cv' = Context_view.extend cv ns in
    if implicit
    then Printf.sprintf "(fun {%s} => %s)" ns (pp_term cv' bound)
    else Printf.sprintf "(fun %s => %s)" ns (pp_term cv' bound)
  | Core.TypedLambda ({ name; bound; implicit }, body) ->
    let ns = Name.to_string name in
    let cv' = Context_view.extend cv ns in
    let l, r = if implicit then "{", "}" else "(", ")" in
    Printf.sprintf "(fun %s%s : %s%s => %s)" l ns (pp_term cv bound) r (pp_term cv' body)
  | Core.Pi ({ name; bound; implicit }, body) ->
    let ns = Name.to_string name in
    let cv' = Context_view.extend cv ns in
    let l, r = if implicit then "{", "}" else "(", ")" in
    Printf.sprintf "%s%s : %s%s -> %s" l ns (pp_term cv bound) r (pp_term cv' body)
  | Core.Meta m -> pp_metavar m
  | Core.InsertedMeta (m, n) -> Printf.sprintf "%s[..%d]" (pp_metavar m) n
  | Core.Lift { from_lvl; to_lvl; ty } ->
    Printf.sprintf "lift[%s→%s] %s" (pp_level from_lvl) (pp_level to_lvl) (pp_term cv ty)
  | Core.LiftTerm { from_lvl; to_lvl; ty; tm } ->
    Printf.sprintf
      "liftₜ[%s→%s] (%s : %s)"
      (pp_level from_lvl)
      (pp_level to_lvl)
      (pp_term cv tm)
      (pp_term cv ty)
  | Core.UnliftTerm { from_lvl; to_lvl; ty; tm } ->
    Printf.sprintf
      "unliftₜ[%s→%s] (%s : %s)"
      (pp_level from_lvl)
      (pp_level to_lvl)
      (pp_term cv tm)
      (pp_term cv ty)
  | Core.RecordType { name; params; fields } ->
    let p_params = List.map (pp_term cv) params in
    let rec walk cv = function
      | [] -> []
      | (b : Core.typ Syntax.binder) :: rest ->
        let t_str = pp_term cv b.bound in
        let bs = Name.to_string b.name in
        let cv' = Context_view.extend cv bs in
        (bs ^ " : " ^ t_str) :: walk cv' rest
    in
    let field_strs = walk cv fields in
    let p =
      match p_params with
      | [] -> ""
      | _ -> " " ^ String.concat " " p_params
    in
    let fs = String.concat " " (List.map (fun s -> "| " ^ s) field_strs) in
    Printf.sprintf "(record %s%s %s)" name p fs
  | Core.RecordIntro { name; fields } ->
    let fs =
      String.concat ", " (List.map (fun (f, e) -> f ^ " = " ^ pp_term cv e) fields)
    in
    Printf.sprintf "%s{ %s }" name fs
  | Core.RecordProj { record; field } -> Printf.sprintf "%s.%s" (pp_term cv record) field
  | Core.IdAbsurd t -> Printf.sprintf "id-absurd %s" (pp_term cv t)
  | Core.Empty -> "Empty"
  | Core.Absurd t -> Printf.sprintf "absurd %s" (pp_term cv t)

and pp_term_arg (cv : Context_view.t) (t : Core.term) : string =
  match t with
  | Core.Universe _ | Core.LocalVar _ | Core.Var _ | Core.Meta _ -> pp_term cv t
  | _ -> "(" ^ pp_term cv t ^ ")"
;;

let%expect_test "pp_universe on LZero" =
  print_string (pp_universe Level.LZero);
  [%expect {| universe 𝓤₀ |}]
;;

let%expect_test "pp_value on a RigidLocal with a known name" =
  let cv = Context_view.extend Context_view.empty "x" in
  let v = Core.RigidLocal (0, Emp) in
  print_string (pp_value cv v);
  [%expect {| x |}]
;;

let%expect_test "pp_value on a Pi prints binder by name" =
  let cv = Context_view.empty in
  let body_closure _ = Core.Universe Level.LZero in
  let ty =
    Core.VPi
      ( { name = Named "n"; bound = Core.IndType ("Nat", Emp); implicit = false }
      , body_closure )
  in
  print_string (pp_value cv ty);
  [%expect {| (n : Nat) -> universe 𝓤₀ |}]
;;

let%expect_test "pp_term renders LocalVar by binder name via index" =
  let cv = Context_view.extend (Context_view.extend Context_view.empty "n") "x" in
  print_string (pp_term cv (Core.LocalVar 0) ^ ", " ^ pp_term cv (Core.LocalVar 1));
  [%expect {| x, n |}]
;;

let%expect_test "pp_term renders Pi with binder name" =
  let cv = Context_view.empty in
  let ty =
    Core.Pi
      ( { name = Named "n"; bound = Core.Var "Nat"; implicit = false }
      , Core.Universe Level.LZero )
  in
  print_string (pp_term cv ty);
  [%expect {| (n : Nat) -> universe 𝓤₀ |}]
;;
