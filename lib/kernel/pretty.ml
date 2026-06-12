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

(* A notation hook lets the caller render a named head applied to explicit
   arguments as user-defined operator syntax. [pp_arg] is the recursive
   argument printer — context- and notation-aware, parenthesizing non-atomic
   arguments. Return [None] to fall back to the default rendering. *)
type 'a notation_hook =
  pp_arg:('a -> string) -> head:string -> explicit_args:'a list -> string option

let rec pp_value ?notation (cv : Context_view.t) (v : Core.value) : string =
  match v with
  | Core.Universe l -> pp_universe l
  | Core.RigidLocal (lvl, spine) -> pp_neutral ?notation cv (pp_local_name cv lvl) spine
  | Core.Var (n, spine) -> pp_named_neutral ?notation cv n spine
  | Core.IndType (n, spine) -> pp_named_neutral ?notation cv n spine
  | Core.Label (n, spine) -> pp_named_neutral ?notation cv n spine
  | Core.Flex (m, spine) -> pp_neutral ?notation cv (pp_metavar m) spine
  | Core.Elim ({ elim_name; _ }, spine) -> pp_named_neutral ?notation cv elim_name spine
  | Core.VPi ({ name; bound; implicit }, closure) ->
    let body = closure (Core.RigidLocal (Context_view.lvl cv, Emp)) in
    let ns = Name.to_string name in
    let cv' = Context_view.extend cv ns in
    let l, r = if implicit then "{", "}" else "(", ")" in
    Printf.sprintf
      "%s%s : %s%s -> %s"
      l
      ns
      (pp_value ?notation cv bound)
      r
      (pp_value ?notation cv' body)
  | Core.VLambda { name; bound = closure; implicit } ->
    let body = closure (Core.RigidLocal (Context_view.lvl cv, Emp)) in
    let ns = Name.to_string name in
    let cv' = Context_view.extend cv ns in
    if implicit
    then Printf.sprintf "(fun {%s} => %s)" ns (pp_value ?notation cv' body)
    else Printf.sprintf "(fun %s => %s)" ns (pp_value ?notation cv' body)
  | Core.VLift { from_lvl; to_lvl; ty } ->
    Printf.sprintf
      "lift[%s→%s] %s"
      (pp_level from_lvl)
      (pp_level to_lvl)
      (pp_value ?notation cv ty)
  | Core.VLiftTerm { from_lvl; to_lvl; ty; tm } ->
    Printf.sprintf
      "liftₜ[%s→%s] (%s : %s)"
      (pp_level from_lvl)
      (pp_level to_lvl)
      (pp_value ?notation cv tm)
      (pp_value ?notation cv ty)
  | Core.VUnliftTerm { from_lvl; to_lvl; ty; tm } ->
    Printf.sprintf
      "unliftₜ[%s→%s] (%s : %s)"
      (pp_level from_lvl)
      (pp_level to_lvl)
      (pp_value ?notation cv tm)
      (pp_value ?notation cv ty)
  | Core.VRecordType { name; params; fields; _ } ->
    let p_params = List.map (pp_value ?notation cv) params in
    let rec walk cv = function
      | [] -> []
      | (b : Core.value_ty Syntax.binder) :: rest ->
        let t_str = pp_value ?notation cv b.bound in
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
      String.concat
        " | "
        (List.map (fun (f, v) -> f ^ " => " ^ pp_value ?notation cv v) fields)
    in
    Printf.sprintf "%s{ %s }" name fs
  | Core.VRecordProj (v, f, sp) ->
    pp_neutral ?notation cv (Printf.sprintf "%s.%s" (pp_value ?notation cv v) f) sp
  | Core.VIdAbsurd v -> Printf.sprintf "id-absurd %s" (pp_value ?notation cv v)
  | Core.VEmpty -> "Empty"
  | Core.VAbsurd (s, sp) ->
    pp_neutral ?notation cv (Printf.sprintf "absurd %s" (pp_value ?notation cv s)) sp

(* Named-global heads (Var / IndType / Label / Elim) give the notation hook
   first shot; local or computed heads must never sugar. *)
and pp_named_neutral ?notation (cv : Context_view.t) (head : string) (spine : Core.spine)
  : string
  =
  let fallback () = pp_neutral ?notation cv head spine in
  match notation with
  | None -> fallback ()
  | Some hook ->
    let explicit =
      List.filter (fun (a : Core.arg) -> not a.implicit) (Bwd.to_list spine)
    in
    (match explicit with
     | [] -> fallback ()
     | args ->
       (match
          hook
            ~pp_arg:(fun v -> pp_arg ?notation cv v)
            ~head
            ~explicit_args:(List.map (fun (a : Core.arg) -> a.tm) args)
        with
        | Some s -> s
        | None -> fallback ()))

and pp_neutral ?notation (cv : Context_view.t) (head : string) (spine : Core.spine)
  : string
  =
  (* implicit arguments 隱藏的目的是讓 goal target 可閱讀 *)
  let explicit = List.filter (fun (a : Core.arg) -> not a.implicit) (Bwd.to_list spine) in
  match explicit with
  | [] -> head
  | args ->
    head
    ^ " "
    ^ String.concat " " (List.map (fun (a : Core.arg) -> pp_arg ?notation cv a.tm) args)

and pp_arg ?notation (cv : Context_view.t) (v : Core.value) : string =
  match v with
  | Core.Universe _
  | Core.RigidLocal (_, Emp)
  | Core.Var (_, Emp)
  | Core.IndType (_, Emp)
  | Core.Label (_, Emp)
  | Core.Flex (_, Emp) -> pp_value ?notation cv v
  | _ -> "(" ^ pp_value ?notation cv v ^ ")"
;;

let rec pp_term ?notation (cv : Context_view.t) (t : Core.term) : string =
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
    let default () =
      match explicit with
      | [] -> pp_term ?notation cv head
      | _ ->
        pp_term ?notation cv head
        ^ " "
        ^ String.concat " " (List.map (fun (a, _) -> pp_term_arg ?notation cv a) explicit)
    in
    (* a named-global head gives the notation hook first shot *)
    (match head, notation, explicit with
     | Core.Var n, Some hook, _ :: _ ->
       (match
          hook
            ~pp_arg:(fun a -> pp_term_arg ?notation cv a)
            ~head:n
            ~explicit_args:(List.map fst explicit)
        with
        | Some s -> s
        | None -> default ())
     | _ -> default ())
  | Core.Lambda { name; bound; implicit } ->
    let ns = Name.to_string name in
    let cv' = Context_view.extend cv ns in
    if implicit
    then Printf.sprintf "(fun {%s} => %s)" ns (pp_term ?notation cv' bound)
    else Printf.sprintf "(fun %s => %s)" ns (pp_term ?notation cv' bound)
  | Core.TypedLambda ({ name; bound; implicit }, body) ->
    let ns = Name.to_string name in
    let cv' = Context_view.extend cv ns in
    let l, r = if implicit then "{", "}" else "(", ")" in
    Printf.sprintf
      "(fun %s%s : %s%s => %s)"
      l
      ns
      (pp_term ?notation cv bound)
      r
      (pp_term ?notation cv' body)
  | Core.Pi ({ name; bound; implicit }, body) ->
    let ns = Name.to_string name in
    let cv' = Context_view.extend cv ns in
    let l, r = if implicit then "{", "}" else "(", ")" in
    Printf.sprintf
      "%s%s : %s%s -> %s"
      l
      ns
      (pp_term ?notation cv bound)
      r
      (pp_term ?notation cv' body)
  | Core.Meta m -> pp_metavar m
  | Core.InsertedMeta (m, n) -> Printf.sprintf "%s[..%d]" (pp_metavar m) n
  | Core.Lift { from_lvl; to_lvl; ty } ->
    Printf.sprintf
      "lift[%s→%s] %s"
      (pp_level from_lvl)
      (pp_level to_lvl)
      (pp_term ?notation cv ty)
  | Core.LiftTerm { from_lvl; to_lvl; ty; tm } ->
    Printf.sprintf
      "liftₜ[%s→%s] (%s : %s)"
      (pp_level from_lvl)
      (pp_level to_lvl)
      (pp_term ?notation cv tm)
      (pp_term ?notation cv ty)
  | Core.UnliftTerm { from_lvl; to_lvl; ty; tm } ->
    Printf.sprintf
      "unliftₜ[%s→%s] (%s : %s)"
      (pp_level from_lvl)
      (pp_level to_lvl)
      (pp_term ?notation cv tm)
      (pp_term ?notation cv ty)
  | Core.RecordType { name; params; fields } ->
    let p_params = List.map (pp_term ?notation cv) params in
    let rec walk cv = function
      | [] -> []
      | (b : Core.typ Syntax.binder) :: rest ->
        let t_str = pp_term ?notation cv b.bound in
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
      String.concat
        " | "
        (List.map (fun (f, e) -> f ^ " => " ^ pp_term ?notation cv e) fields)
    in
    Printf.sprintf "%s{ %s }" name fs
  | Core.RecordProj { record; field } ->
    Printf.sprintf "%s.%s" (pp_term ?notation cv record) field
  | Core.IdAbsurd t -> Printf.sprintf "id-absurd %s" (pp_term ?notation cv t)
  | Core.Empty -> "Empty"
  | Core.Absurd t -> Printf.sprintf "absurd %s" (pp_term ?notation cv t)

and pp_term_arg ?notation (cv : Context_view.t) (t : Core.term) : string =
  match t with
  | Core.Universe _ | Core.LocalVar _ | Core.Var _ | Core.Meta _ -> pp_term ?notation cv t
  | Core.App _ ->
    (* an application whose arguments are ALL implicit renders as its bare
       head — don't wrap an invisible spine in parens *)
    let rec collect t acc =
      match t with
      | Core.App (f, a, implicit) -> collect f ((a, implicit) :: acc)
      | _ -> t, acc
    in
    let head, args = collect t [] in
    (match head, List.exists (fun (_, implicit) -> not implicit) args with
     | (Core.Universe _ | Core.LocalVar _ | Core.Var _ | Core.Meta _), false ->
       pp_term ?notation cv t
     | _ -> "(" ^ pp_term ?notation cv t ^ ")")
  | _ -> "(" ^ pp_term ?notation cv t ^ ")"
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

(* --- notation hook tests ------------------------------------------------ *)

let test_hook ~pp_arg ~head ~explicit_args =
  match head, explicit_args with
  | "Id", [ a; b ] -> Some (pp_arg a ^ " = " ^ pp_arg b)
  | _ -> None
;;

let%expect_test "pp_term: notation hook sugars an Id spine" =
  let id a b = Core.App (Core.App (Core.Var "Id", a, false), b, false) in
  let t = id (Core.Var "a") (Core.Var "b") in
  print_string (pp_term ~notation:test_hook Context_view.empty t);
  [%expect {| a = b |}]
;;

let%expect_test "pp_term: nested operator argument is parenthesized" =
  let id a b = Core.App (Core.App (Core.Var "Id", a, false), b, false) in
  let t = id (id (Core.Var "a") (Core.Var "b")) (Core.Var "c") in
  print_string (pp_term ~notation:test_hook Context_view.empty t);
  [%expect {| (a = b) = c |}]
;;

let%expect_test "pp_term: hook sees only explicit args" =
  let t =
    Core.App
      ( Core.App (Core.App (Core.Var "Id", Core.Var "A", true), Core.Var "x", false)
      , Core.Var "y"
      , false )
  in
  print_string (pp_term ~notation:test_hook Context_view.empty t);
  [%expect {| x = y |}]
;;

let%expect_test "pp_term: non-matching head falls back to raw application" =
  let t =
    Core.App (Core.App (Core.Var "add", Core.Var "a", false), Core.Var "b", false)
  in
  print_string (pp_term ~notation:test_hook Context_view.empty t);
  [%expect {| add a b |}]
;;

let%expect_test "pp_term: implicit-only application is a bare argument" =
  (* `empty {s}` in argument position must print `f empty`, not `f (empty)` *)
  let t =
    Core.App (Core.Var "f", Core.App (Core.Var "empty", Core.Var "s", true), false)
  in
  print_string (pp_term Context_view.empty t);
  [%expect {| f empty |}]
;;

let%expect_test "pp_value: notation hook sugars an IndType neutral" =
  let v =
    let open Bwd.Infix in
    Core.IndType
      ( "Id"
      , Emp
        <: Core.implicit_arg (Core.Var ("A", Emp))
        <: Core.explicit_arg (Core.Var ("x", Emp))
        <: Core.explicit_arg (Core.Var ("y", Emp)) )
  in
  print_string (pp_value ~notation:test_hook Context_view.empty v);
  [%expect {| x = y |}]
;;
