open Syntax
open Bwd

let pp_local_name (cv : Context_view.t) (lvl : int) : string =
  match Context_view.nth_name_from_lvl cv lvl with
  | Some n -> n
  | None -> Printf.sprintf "$%d" lvl
;;

let rec pp_level_atom (l : Level.level) : string =
  match l with
  | Level.LZero -> "0"
  | Level.LVar v -> v
  | Level.LSuc _ | Level.LMax _ -> "(" ^ pp_level l ^ ")"

and pp_level (l : Level.level) : string =
  match l with
  | Level.LZero -> "0"
  | Level.LVar v -> v
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
    let cv' = Context_view.extend cv name in
    let l, r = if implicit then "{", "}" else "(", ")" in
    Printf.sprintf "%s%s : %s%s -> %s" l name (pp_value cv bound) r (pp_value cv' body)
  | Core.VLambda { name; bound = closure; implicit } ->
    let body = closure (Core.RigidLocal (Context_view.lvl cv, Emp)) in
    let cv' = Context_view.extend cv name in
    if implicit
    then Printf.sprintf "(fun {%s} => %s)" name (pp_value cv' body)
    else Printf.sprintf "(fun %s => %s)" name (pp_value cv' body)
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
        let cv' = Context_view.extend cv b.name in
        (b.name ^ " : " ^ t_str) :: walk cv' rest
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
  | Core.VRecordProj (v, f) -> Printf.sprintf "%s.%s" (pp_value cv v) f
  | Core.VIdAbsurd v -> Printf.sprintf "id-absurd %s" (pp_value cv v)

and pp_neutral (cv : Context_view.t) (head : string) (spine : Core.value bwd) : string =
  if Bwd.is_empty spine
  then head
  else (
    let args = List.map (pp_arg cv) (Bwd.to_list spine) in
    head ^ " " ^ String.concat " " args)

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
      ({ name = "n"; bound = Core.IndType ("Nat", Emp); implicit = false }, body_closure)
  in
  print_string (pp_value cv ty);
  [%expect {| (n : Nat) -> universe 𝓤₀ |}]
;;
