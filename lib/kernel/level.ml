(* Levels are normalized to the form
     max(k₀, k₁ + v₁, k₂ + v₂, …)
   where k₀ ≥ 0 is a constant offset and each (kᵢ, vᵢ) is a distinct level
   variable name with offset kᵢ ≥ 0.  The variables are kept sorted by name
   for canonical comparison. *)

type atom =
  { var : string
  ; offset : int (* "n + offset" where n is the value of var *)
  }
[@@deriving show]

type nf =
  { const : int
  ; atoms : atom list (* sorted by var, distinct *)
  }
[@@deriving show]

type level =
  | LZero
  | LVar of string
  | LSuc of level
  | LMax of level * level
  | LMeta of int
[@@deriving show]

let level_meta_store : (int, level) Hashtbl.t = Hashtbl.create ~random:true 16
let level_meta_count = ref 0

let fresh_level_meta () : level =
  let i = !level_meta_count in
  incr level_meta_count;
  LMeta i
;;

let solve_level_meta (i : int) (l : level) : unit = Hashtbl.replace level_meta_store i l

let rec force_level (l : level) : level =
  match l with
  | LMeta i ->
    (match Hashtbl.find_opt level_meta_store i with
     | Some l' -> force_level l'
     | None -> l)
  | _ -> l
;;

let lzero : level = LZero
let lvar (s : string) : level = LVar s
let lsuc (l : level) : level = LSuc l
let lmax (a : level) (b : level) : level = LMax (a, b)

let rec pretty : level -> string = function
  | LZero -> "𝓤₀"
  | LVar v -> v
  | LSuc l -> "(" ^ pretty l ^ "+1)"
  | LMax (a, b) -> pretty a ^ " ⊔ " ^ pretty b
  | LMeta i ->
    (match Hashtbl.find_opt level_meta_store i with
     | Some l -> pretty l
     | None -> Printf.sprintf "?lvl%d" i)
;;

let normalize (l : level) : nf =
  let rec go (offset : int) (acc_const : int) (acc_atoms : atom list) = function
    | LZero -> max acc_const offset, acc_atoms
    | LVar v ->
      ( acc_const
      , let entry = { var = v; offset } in
        let rec insert = function
          | [] -> [ entry ]
          | (a : atom) :: rest when a.var = v ->
            { var = v; offset = max a.offset offset } :: rest
          | (a : atom) :: rest when a.var > v -> entry :: a :: rest
          | a :: rest -> a :: insert rest
        in
        insert acc_atoms )
    | LSuc inner -> go (offset + 1) acc_const acc_atoms inner
    | LMax (a, b) ->
      let c1, ats1 = go offset acc_const acc_atoms a in
      go offset c1 ats1 b
    | LMeta i ->
      (match Hashtbl.find_opt level_meta_store i with
       | Some l' -> go offset acc_const acc_atoms l'
       | None ->
         let tag = Printf.sprintf "?lvl%d" i in
         ( acc_const
         , let entry = { var = tag; offset } in
           let rec insert = function
             | [] -> [ entry ]
             | (a : atom) :: rest when a.var = tag ->
               { var = tag; offset = max a.offset offset } :: rest
             | (a : atom) :: rest when a.var > tag -> entry :: a :: rest
             | a :: rest -> a :: insert rest
           in
           insert acc_atoms ))
  in
  let c, atoms = go 0 0 [] l in
  { const = c; atoms }
;;

let equal (a : level) (b : level) : bool =
  let a = force_level a in
  let b = force_level b in
  let na = normalize a in
  let nb = normalize b in
  na.const = nb.const
  && List.length na.atoms = List.length nb.atoms
  && List.for_all2
       (fun (x : atom) (y : atom) -> x.var = y.var && x.offset = y.offset)
       na.atoms
       nb.atoms
;;

let not_equal (a : level) (b : level) : bool = not (equal a b)

(* Decidable ≤: every summand on LHS must be ≤ some summand on RHS.
   For each LHS atom (v, off), the RHS must have an atom (v, off') with
   off ≤ off'.  Distinct variables are independent, so no LHS atom (v, _)
   can be discharged by a different variable on the right or by the constant
   on the right.  However, the LHS constant c can be discharged by any RHS
   atom (w, j) with c ≤ j, since w ≥ 0 implies (w + j) ≥ j ≥ c. *)
let le (a : level) (b : level) : bool =
  let a = force_level a in
  let b = force_level b in
  let na = normalize a in
  let nb = normalize b in
  let const_ok =
    na.const <= nb.const || List.exists (fun (y : atom) -> na.const <= y.offset) nb.atoms
  in
  let atom_ok =
    List.for_all
      (fun (x : atom) ->
         List.exists (fun (y : atom) -> y.var = x.var && x.offset <= y.offset) nb.atoms)
      na.atoms
  in
  const_ok && atom_ok
;;

exception Level_unify_error of string

let rec unify_level (a : level) (b : level) : unit =
  let a = force_level a in
  let b = force_level b in
  match a, b with
  | LMeta i, l | l, LMeta i -> solve_level_meta i l
  | LZero, LZero -> ()
  | LVar v1, LVar v2 when v1 = v2 -> ()
  | LSuc l1, LSuc l2 -> unify_level l1 l2
  | LMax (a1, b1), LMax (a2, b2) ->
    unify_level a1 a2;
    unify_level b1 b2
  | l1, l2 ->
    raise
      (Level_unify_error
         (Printf.sprintf "cannot unify level `%s` with `%s`" (pretty l1) (pretty l2)))
;;

let subst_level_var (from_var : string) (to_level : level) (l : level) : level =
  let rec go = function
    | LZero -> LZero
    | LVar v -> if v = from_var then to_level else LVar v
    | LSuc l -> LSuc (go l)
    | LMax (a, b) -> LMax (go a, go b)
    | LMeta i ->
      (match Hashtbl.find_opt level_meta_store i with
       | Some l' -> go l'
       | None -> LMeta i)
  in
  go l
;;

let%expect_test "normalize zero" =
  print_string @@ show_nf (normalize LZero);
  [%expect {| { Level.const = 0; atoms = [] } |}]
;;

let%expect_test "normalize suc(suc zero) = 2" =
  print_string @@ show_nf (normalize (LSuc (LSuc LZero)));
  [%expect {| { Level.const = 2; atoms = [] } |}]
;;

let%expect_test "normalize suc(LVar U) = U + 1" =
  print_string @@ show_nf (normalize (LSuc (LVar "U")));
  [%expect {| { Level.const = 0; atoms = [{ Level.var = "U"; offset = 1 }] } |}]
;;

let%expect_test "normalize max(U, V)" =
  print_string @@ show_nf (normalize (LMax (LVar "U", LVar "V")));
  [%expect
    {|
    { Level.const = 0;
      atoms = [{ Level.var = "U"; offset = 0 }; { Level.var = "V"; offset = 0 }]
      }
    |}]
;;

let%expect_test "normalize max(U, U) = U" =
  print_string @@ show_nf (normalize (LMax (LVar "U", LVar "U")));
  [%expect {| { Level.const = 0; atoms = [{ Level.var = "U"; offset = 0 }] } |}]
;;

let%expect_test "normalize max(suc U, U) merges to U+1" =
  print_string @@ show_nf (normalize (LMax (LSuc (LVar "U"), LVar "U")));
  [%expect {| { Level.const = 0; atoms = [{ Level.var = "U"; offset = 1 }] } |}]
;;

let%expect_test "equal: U = U" =
  print_string @@ string_of_bool (equal (LVar "U") (LVar "U"));
  [%expect {| true |}]
;;

let%expect_test "equal: U ≠ V" =
  print_string @@ string_of_bool (equal (LVar "U") (LVar "V"));
  [%expect {| false |}]
;;

let%expect_test "equal: suc(suc zero) = 2" =
  print_string @@ string_of_bool (equal (LSuc (LSuc LZero)) (LSuc (LSuc LZero)));
  [%expect {| true |}]
;;

let%expect_test "le: 0 ≤ U" =
  print_string @@ string_of_bool (le LZero (LVar "U"));
  [%expect {| true |}]
;;

let%expect_test "le: U ≤ suc U" =
  print_string @@ string_of_bool (le (LVar "U") (LSuc (LVar "U")));
  [%expect {| true |}]
;;

let%expect_test "le: U ≰ V" =
  print_string @@ string_of_bool (le (LVar "U") (LVar "V"));
  [%expect {| false |}]
;;

let%expect_test "le: U ≤ max(U, V)" =
  print_string @@ string_of_bool (le (LVar "U") (LMax (LVar "U", LVar "V")));
  [%expect {| true |}]
;;

let%expect_test "le: max(U, V) ≤ max(U, V)" =
  print_string
  @@ string_of_bool (le (LMax (LVar "U", LVar "V")) (LMax (LVar "U", LVar "V")));
  [%expect {| true |}]
;;

let%expect_test "le: suc U ≰ U (offset matters)" =
  print_string @@ string_of_bool (le (LSuc (LVar "U")) (LVar "U"));
  [%expect {| false |}]
;;

let%expect_test "le: U ≰ max(V, W) (distinct vars don't discharge)" =
  print_string @@ string_of_bool (le (LVar "U") (LMax (LVar "V", LVar "W")));
  [%expect {| false |}]
;;

let%expect_test "le: suc 0 ≰ U (U could be 0)" =
  print_string @@ string_of_bool (le (LSuc LZero) (LVar "U"));
  [%expect {| false |}]
;;

let%expect_test "le: 1 ≤ suc U (U ≥ 0 so U+1 ≥ 1)" =
  print_string @@ string_of_bool (le (LSuc LZero) (LSuc (LVar "U")));
  [%expect {| true |}]
;;
