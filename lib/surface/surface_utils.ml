open Violet_kernel.Syntax

let rec loc_of : Surface.preterm -> Asai.Range.t option = function
  | Surface.Located { loc; value } ->
    (match loc_of value with
     | Some _ as inner -> inner
     | None -> loc)
  | _ -> None
;;

let rec peel_pi_surface ~(loc : Asai.Range.t) (n : int) (s : Surface.pretype)
  : Surface.pretype
  =
  if n = 0
  then s
  else (
    match s with
    | Surface.Located { value; loc = inner } ->
      peel_pi_surface ~loc:(Option.value inner ~default:loc) n value
    | Surface.Pi (_, cod) -> peel_pi_surface ~loc (n - 1) cod
    | _ ->
      Reporter.fatalf
        ~loc
        Elab_error
        "stack-def: signature has fewer Pi-layers than required (%d remaining)"
        n)
;;

let linearize_pi (t : Surface.pretype) : Surface.pretype binder list * Surface.pretype =
  let rec go acc t =
    match t with
    | Surface.Located { value; _ } -> go acc value
    | Surface.Pi (b, body) -> go (b :: acc) body
    | _ -> List.rev acc, t
  in
  go [] t
;;

let pi_domain (t : Surface.pretype) : Surface.pretype binder list = fst (linearize_pi t)

let rec head_of_surface = function
  | Surface.App (_, f, _) -> head_of_surface f
  | Surface.Located { value = t; _ } -> head_of_surface t
  | t -> t
;;

let occurs_in (target : string) (t : Surface.preterm) : bool =
  let rec go t =
    match t with
    | Surface.Located { value = u; _ } -> go u
    | Surface.Var [ n ] -> String.equal n target
    | Surface.Var _ -> false
    | Surface.App (_, f, x) -> go f || go x
    | Surface.Pi (b, body) -> go b.bound || ((not (b.name = Named target)) && go body)
    (* Surface.Lambda has no type annotation; `b.bound` is the body. *)
    | Surface.Lambda b -> (not (b.name = Named target)) && go b.bound
    | Surface.TypedLambda (b, body) ->
      go b.bound || ((not (b.name = Named target)) && go body)
    | Surface.Max (a, b) -> go a || go b
    | Surface.Universe | Surface.Hole | Surface.Goal _ -> false
    | Surface.IdAbsurd _ -> false
    | Surface.Absurd _ -> false
    | Surface.Op_soup _ ->
      Reporter.fatalf
        Elab_error
        "internal: Op_soup reached occurs_in (resolver should have lowered it)"
    | Surface.RecordLit entries -> List.exists (fun (_, e) -> go e) entries
    | Surface.RecordUpdate (base, entries) ->
      go base || List.exists (fun (_, e) -> go e) entries
    | Surface.Proj (e, _) -> go e
    | Surface.Inline_elim d -> String.equal d.target target
  in
  go t
;;

let head_and_spine (t : Surface.preterm) : Surface.preterm * Surface.preterm list =
  let rec go t acc =
    match t with
    | Surface.Located { value = u; _ } -> go u acc
    | Surface.App (_, f, x) -> go f (x :: acc)
    | h -> h, acc
  in
  go t []
;;

let map_free_vars
      (type s)
      ~(on_var : s -> string -> Surface.preterm)
      ~(enter : string -> s -> s)
      (scope : s)
      (t : Surface.preterm)
  : Surface.preterm
  =
  let enter_bn (nm : Surface.binder_name) scope =
    match nm with
    | Anon -> scope
    | Named n -> enter n scope
  in
  let rec go scope t =
    match t with
    | Surface.Located { value; loc } -> Surface.Located { value = go scope value; loc }
    | Surface.Var [ n ] -> on_var scope n
    | Surface.Var _ -> t
    | Surface.App (impl, f, a) -> Surface.App (impl, go scope f, go scope a)
    | Surface.Lambda b ->
      Surface.Lambda { b with bound = go (enter_bn b.name scope) b.bound }
    | Surface.TypedLambda (b, body) ->
      let bound' = go scope b.bound in
      Surface.TypedLambda ({ b with bound = bound' }, go (enter_bn b.name scope) body)
    | Surface.Pi (b, body) ->
      let bound' = go scope b.bound in
      Surface.Pi ({ b with bound = bound' }, go (enter_bn b.name scope) body)
    | Surface.Max (a, b) -> Surface.Max (go scope a, go scope b)
    | Surface.Universe | Surface.Hole | Surface.Goal _ -> t
    | Surface.IdAbsurd p -> Surface.IdAbsurd (go scope p)
    | Surface.Absurd p -> Surface.Absurd (go scope p)
    | Surface.Op_soup _ ->
      Reporter.fatalf
        Elab_error
        "internal: Op_soup reached map_free_vars (resolver should have lowered it)"
    | Surface.RecordLit entries ->
      Surface.RecordLit (List.map (fun (f, e) -> f, go scope e) entries)
    | Surface.RecordUpdate (base, entries) ->
      Surface.RecordUpdate (go scope base, List.map (fun (f, e) -> f, go scope e) entries)
    | Surface.Proj (e, f) -> Surface.Proj (go scope e, f)
    | Surface.Inline_elim _ as t -> t
  in
  go scope t
;;

let%expect_test "occurs_in: Var present" =
  let t = Surface.Var [ "Bad" ] in
  print_string @@ string_of_bool (occurs_in "Bad" t);
  [%expect {| true |}]
;;

let%expect_test "occurs_in: Var absent" =
  let t = Surface.Var [ "Other" ] in
  print_string @@ string_of_bool (occurs_in "Bad" t);
  [%expect {| false |}]
;;

let%expect_test "occurs_in: under App argument" =
  let t = Surface.apply (Surface.Var [ "List" ]) [ Surface.Var [ "Bad" ] ] in
  print_string @@ string_of_bool (occurs_in "Bad" t);
  [%expect {| true |}]
;;

let%expect_test "occurs_in: under Pi domain" =
  let t =
    Surface.Pi
      ( { Violet_kernel.Syntax.name = Anon
        ; bound = Surface.Var [ "Bad" ]
        ; implicit = false
        }
      , Surface.Var [ "X" ] )
  in
  print_string @@ string_of_bool (occurs_in "Bad" t);
  [%expect {| true |}]
;;

let%expect_test "occurs_in: shadowed by inner binder" =
  let t =
    Surface.Pi
      ( { Violet_kernel.Syntax.name = Named "Bad"
        ; bound = Surface.Universe
        ; implicit = false
        }
      , Surface.Var [ "Bad" ] )
  in
  print_string @@ string_of_bool (occurs_in "Bad" t);
  (* Bad in domain (Universe) doesn't match; in body, Bad is shadowed → no. *)
  [%expect {| false |}]
;;

let%expect_test "occurs_in: Lambda shadows" =
  let t =
    Surface.Lambda
      { Violet_kernel.Syntax.name = Named "Bad"
      ; bound = Surface.Var [ "Bad" ]
      ; implicit = false
      }
  in
  print_string @@ string_of_bool (occurs_in "Bad" t);
  (* Body's `Bad` is shadowed by the lambda binder → no. *)
  [%expect {| false |}]
;;

let%expect_test "head_and_spine: bare var" =
  let h, sp = head_and_spine (Surface.Var [ "Nat" ]) in
  Format.printf "%s/%d" ([%show: Surface.preterm] h) (List.length sp);
  [%expect {| Nat/0 |}]
;;

let%expect_test "head_and_spine: applied" =
  let t =
    Surface.apply (Surface.Var [ "Vec" ]) [ Surface.Var [ "A" ]; Surface.Var [ "n" ] ]
  in
  let h, sp = head_and_spine t in
  Format.printf "%s/%d" ([%show: Surface.preterm] h) (List.length sp);
  [%expect {| Vec/2 |}]
;;
