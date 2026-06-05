open Violet_kernel.Syntax

let rec peel_pi_surface (n : int) (s : Surface.pretype) : Surface.pretype =
  if n = 0
  then s
  else (
    match s.Surface.node with
    | Surface.Pi (_, cod) -> peel_pi_surface (n - 1) cod
    | _ ->
      Reporter.fatalf
        ~loc:s.Surface.loc
        Elab_error
        "stack-def: signature has fewer Pi-layers than required (%d remaining)"
        n)
;;

let linearize_pi (t : Surface.pretype)
  : Surface.pretype Surface.sbinder list * Surface.pretype
  =
  let rec go acc (t : Surface.pretype) =
    match t.Surface.node with
    | Surface.Pi (b, body) -> go (b :: acc) body
    | _ -> List.rev acc, t
  in
  go [] t
;;

let pi_domain (t : Surface.pretype) : Surface.pretype Surface.sbinder list =
  fst (linearize_pi t)
;;

let rec head_of_surface (t : Surface.preterm) : Surface.preterm =
  match t.Surface.node with
  | Surface.App (_, f, _) -> head_of_surface f
  | _ -> t
;;

let occurs_in (target : string) (t : Surface.preterm) : bool =
  let rec go (t : Surface.preterm) =
    match t.Surface.node with
    | Surface.Var [ n ] -> String.equal n target
    | Surface.Var _ -> false
    | Surface.App (_, f, x) -> go f || go x
    | Surface.Pi (b, body) ->
      go b.bound || ((not (b.name.Surface.value = Named target)) && go body)
    (* Surface.Lambda has no type annotation; `b.bound` is the body. *)
    | Surface.Lambda b -> (not (b.name.Surface.value = Named target)) && go b.bound
    | Surface.TypedLambda (b, body) ->
      go b.bound || ((not (b.name.Surface.value = Named target)) && go body)
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
  let rec go (t : Surface.preterm) acc =
    match t.Surface.node with
    | Surface.App (_, f, x) -> go f (x :: acc)
    | _ -> t, acc
  in
  go t []
;;

let map_free_vars
      (type s)
      ~(on_var : loc:Asai.Range.t -> s -> string -> Surface.preterm)
      ~(enter : string -> s -> s)
      (scope : s)
      (t : Surface.preterm)
  : Surface.preterm
  =
  let enter_bn (nm : Surface.binder_name Surface.spanned) scope =
    match nm.Surface.value with
    | Anon -> scope
    | Named n -> enter n scope
  in
  let rec go scope (t : Surface.preterm) =
    match t.Surface.node with
    | Surface.Var [ n ] -> on_var ~loc:t.Surface.loc scope n
    | Surface.Var _ -> t
    | Surface.App (impl, f, a) ->
      { t with Surface.node = Surface.App (impl, go scope f, go scope a) }
    | Surface.Lambda b ->
      { t with
        Surface.node =
          Surface.Lambda { b with bound = go (enter_bn b.name scope) b.bound }
      }
    | Surface.TypedLambda (b, body) ->
      let bound' = go scope b.bound in
      { t with
        Surface.node =
          Surface.TypedLambda ({ b with bound = bound' }, go (enter_bn b.name scope) body)
      }
    | Surface.Pi (b, body) ->
      let bound' = go scope b.bound in
      { t with
        Surface.node =
          Surface.Pi ({ b with bound = bound' }, go (enter_bn b.name scope) body)
      }
    | Surface.Max (a, b) -> { t with Surface.node = Surface.Max (go scope a, go scope b) }
    | Surface.Universe | Surface.Hole | Surface.Goal _ -> t
    | Surface.IdAbsurd p -> { t with Surface.node = Surface.IdAbsurd (go scope p) }
    | Surface.Absurd p -> { t with Surface.node = Surface.Absurd (go scope p) }
    | Surface.Op_soup _ ->
      Reporter.fatalf
        Elab_error
        "internal: Op_soup reached map_free_vars (resolver should have lowered it)"
    | Surface.RecordLit entries ->
      { t with
        Surface.node = Surface.RecordLit (List.map (fun (f, e) -> f, go scope e) entries)
      }
    | Surface.RecordUpdate (base, entries) ->
      { t with
        Surface.node =
          Surface.RecordUpdate
            (go scope base, List.map (fun (f, e) -> f, go scope e) entries)
      }
    | Surface.Proj (e, f) -> { t with Surface.node = Surface.Proj (go scope e, f) }
    | Surface.Inline_elim _ -> t
  in
  go scope t
;;

let d node = Surface.Mk.at Surface.dummy_loc node
let dn name = { Surface.loc = Surface.dummy_loc; Surface.value = name }

let%expect_test "occurs_in: Var present" =
  let t = d (Surface.Var [ "Bad" ]) in
  print_string @@ string_of_bool (occurs_in "Bad" t);
  [%expect {| true |}]
;;

let%expect_test "occurs_in: Var absent" =
  let t = d (Surface.Var [ "Other" ]) in
  print_string @@ string_of_bool (occurs_in "Bad" t);
  [%expect {| false |}]
;;

let%expect_test "occurs_in: under App argument" =
  let t = Surface.apply (d (Surface.Var [ "List" ])) [ d (Surface.Var [ "Bad" ]) ] in
  print_string @@ string_of_bool (occurs_in "Bad" t);
  [%expect {| true |}]
;;

let%expect_test "occurs_in: under Pi domain" =
  let t =
    d
      (Surface.Pi
         ( { Surface.name = dn Surface.Anon
           ; bound = d (Surface.Var [ "Bad" ])
           ; implicit = false
           }
         , d (Surface.Var [ "X" ]) ))
  in
  print_string @@ string_of_bool (occurs_in "Bad" t);
  [%expect {| true |}]
;;

let%expect_test "occurs_in: shadowed by inner binder" =
  let t =
    d
      (Surface.Pi
         ( { Surface.name = dn (Surface.Named "Bad")
           ; bound = d Surface.Universe
           ; implicit = false
           }
         , d (Surface.Var [ "Bad" ]) ))
  in
  print_string @@ string_of_bool (occurs_in "Bad" t);
  (* Bad in domain (Universe) doesn't match; in body, Bad is shadowed → no. *)
  [%expect {| false |}]
;;

let%expect_test "occurs_in: Lambda shadows" =
  let t =
    d
      (Surface.Lambda
         { Surface.name = dn (Surface.Named "Bad")
         ; bound = d (Surface.Var [ "Bad" ])
         ; implicit = false
         })
  in
  print_string @@ string_of_bool (occurs_in "Bad" t);
  (* Body's `Bad` is shadowed by the lambda binder → no. *)
  [%expect {| false |}]
;;

let%expect_test "head_and_spine: bare var" =
  let h, sp = head_and_spine (d (Surface.Var [ "Nat" ])) in
  Format.printf "%s/%d" ([%show: Surface.preterm] h) (List.length sp);
  [%expect {| Nat/0 |}]
;;

let%expect_test "head_and_spine: applied" =
  let t =
    Surface.apply
      (d (Surface.Var [ "Vec" ]))
      [ d (Surface.Var [ "A" ]); d (Surface.Var [ "n" ]) ]
  in
  let h, sp = head_and_spine t in
  Format.printf "%s/%d" ([%show: Surface.preterm] h) (List.length sp);
  [%expect {| Vec/2 |}]
;;
