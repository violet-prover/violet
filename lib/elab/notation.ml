open Violet_surface
module Pretty = Violet_kernel.Pretty
module Context_view = Violet_kernel.Context_view
module Core = Violet_kernel.Syntax.Core

type table = (string, Op_resolver.inv_entry) Hashtbl.t

(* decls is newest-first; walk oldest-first so that when two invertible
   operators share a head the FIRST declaration wins. *)
let table_of_ops (ops : Op_resolver.op_table) : table =
  let tbl : table = Hashtbl.create 16 in
  List.iter
    (fun d ->
       match Op_resolver.invert_decl d with
       | Some e when not (Hashtbl.mem tbl e.Op_resolver.inv_head) ->
         Hashtbl.add tbl e.Op_resolver.inv_head e
       | _ -> ())
    (List.rev ops.Op_resolver.decls);
  (* ALSO key each qualified head under its last path segment: constructor
     VALUES print with bare names (`prepend`, not `Prog/prepend`), so the
     full-path key never matches them. A segment claimed by more than one
     operator (e.g. `cons` for both ◅ and ◁) is ambiguous and gets no alias;
     a segment that already names an operator keeps that operator. *)
  let claims : (string, Op_resolver.inv_entry option) Hashtbl.t = Hashtbl.create 8 in
  Hashtbl.iter
    (fun head e ->
       match String.rindex_opt head '/' with
       | None -> ()
       | Some i ->
         let seg = String.sub head (i + 1) (String.length head - i - 1) in
         (match Hashtbl.find_opt claims seg with
          | None -> Hashtbl.replace claims seg (Some e)
          | Some _ -> Hashtbl.replace claims seg None (* ambiguous *)))
    tbl;
  Hashtbl.iter
    (fun seg e ->
       match e with
       | Some e when not (Hashtbl.mem tbl seg) -> Hashtbl.add tbl seg e
       | _ -> ())
    claims;
  tbl
;;

module R = Algaeff.Reader.Make (struct
    type t = table
  end)

let run ~(module_name : string) f =
  let ops =
    Option.value (Op_resolver.lookup_table ~module_name) ~default:Op_resolver.empty_table
  in
  R.run ~env:(table_of_ops ops) f
;;

let current_table () : table option =
  match R.read () with
  | t -> Some t
  | exception Stdlib.Effect.Unhandled _ -> None
;;

(* Try rendering [head explicit_args] through an operator template. *)
let try_op : type a. table -> pp_arg:(a -> string) -> string -> a list -> string option =
  fun tbl ~pp_arg head explicit_args ->
  match Hashtbl.find_opt tbl head with
  | Some e when List.length explicit_args = e.Op_resolver.inv_arity ->
    let args = Array.of_list explicit_args in
    Some
      (String.concat
         " "
         (List.map
            (function
              | Op_resolver.Inv_lit s -> s
              | Op_resolver.Inv_slot i -> pp_arg args.(i))
            e.Op_resolver.inv_parts))
  | _ -> None
;;

(* ===========================================================================
   Eliminator-spine folding
   ===========================================================================
   NbE delta-unfolds `add n (suc m)` into a stuck `Nat/elim n M Z S (suc m)`
   spine, which is unreadable. A `\let f … <= \elim x` compiles to lambdas
   around an eliminator call whose motive/case arguments are CLOSED terms, so
   at definition time we register a spine template (closed slots + param
   slots) keyed by the eliminator's name, and at print time fold matching
   spines back to `f args…` — on which operator notation then applies. *)
type fold_slot =
  | F_param of int (* index into f's params, 0 = first *)
  | F_closed of Core.term (* name-erased closed term that must match exactly *)

type fold_entry =
  { f_name : string
  ; f_slots : fold_slot list (* one per EXPLICIT argument of the eliminator call *)
  ; f_display : int list (* f's explicit param indices, in declaration order *)
  }

(* eliminator core-name → templates in registration order (first match wins) *)
let fold_registry : (string, fold_entry list) Hashtbl.t = Hashtbl.create 16

(* Structural equality up to binder names: erase every binder_name to Anon so
   print-time quotes compare equal to registration-time quotes. *)
let rec erase_names (t : Core.term) : Core.term =
  match t with
  | Core.Universe _
  | Core.LocalVar _
  | Core.Var _
  | Core.Meta _
  | Core.InsertedMeta _
  | Core.Empty -> t
  | Core.App (f, a, i) -> Core.App (erase_names f, erase_names a, i)
  | Core.Lambda b -> Core.Lambda { b with name = Anon; bound = erase_names b.bound }
  | Core.TypedLambda (b, body) ->
    Core.TypedLambda
      ({ b with name = Anon; bound = erase_names b.bound }, erase_names body)
  | Core.Pi (b, body) ->
    Core.Pi ({ b with name = Anon; bound = erase_names b.bound }, erase_names body)
  | Core.Lift l -> Core.Lift { l with ty = erase_names l.ty }
  | Core.LiftTerm l ->
    Core.LiftTerm { l with ty = erase_names l.ty; tm = erase_names l.tm }
  | Core.UnliftTerm l ->
    Core.UnliftTerm { l with ty = erase_names l.ty; tm = erase_names l.tm }
  | Core.RecordType r ->
    Core.RecordType
      { r with
        params = List.map erase_names r.params
      ; fields =
          List.map
            (fun (b : Core.typ Violet_kernel.Syntax.binder) ->
               { b with name = Anon; bound = erase_names b.bound })
            r.fields
      }
  | Core.RecordIntro r ->
    Core.RecordIntro
      { r with fields = List.map (fun (f, e) -> f, erase_names e) r.fields }
  | Core.RecordProj p -> Core.RecordProj { p with record = erase_names p.record }
  | Core.IdAbsurd t -> Core.IdAbsurd (erase_names t)
  | Core.Absurd t -> Core.Absurd (erase_names t)
;;

(* No reference to any binder OUTSIDE the term: every LocalVar stays below
   the number of binders crossed inside the term itself. *)
let is_closed (t : Core.term) : bool =
  let rec go depth = function
    | Core.LocalVar ix -> ix < depth
    | Core.Universe _ | Core.Var _ | Core.Meta _ | Core.InsertedMeta _ | Core.Empty ->
      true
    | Core.App (f, a, _) -> go depth f && go depth a
    | Core.Lambda b -> go (depth + 1) b.bound
    | Core.TypedLambda (b, body) -> go depth b.bound && go (depth + 1) body
    | Core.Pi (b, body) -> go depth b.bound && go (depth + 1) body
    | Core.Lift l -> go depth l.ty
    | Core.LiftTerm l -> go depth l.ty && go depth l.tm
    | Core.UnliftTerm l -> go depth l.ty && go depth l.tm
    | Core.RecordType r ->
      List.for_all (go depth) r.params
      &&
      let rec fields depth = function
        | [] -> true
        | (b : Core.typ Violet_kernel.Syntax.binder) :: rest ->
          go depth b.bound && fields (depth + 1) rest
      in
      fields depth r.fields
    | Core.RecordIntro r -> List.for_all (fun (_, e) -> go depth e) r.fields
    | Core.RecordProj p -> go depth p.record
    | Core.IdAbsurd t -> go depth t
    | Core.Absurd t -> go depth t
  in
  go 0 t
;;

(* Register a fold template for the definition [fn] whose NORMALIZED body (a
   closed core term, quoted at level 0) is [tm]. Only definitions of the
   shape `fun p₀ … pₖ => <eliminator> args…` register, where every explicit
   eliminator argument is either one of the params (each used at most once)
   or a closed term, and every EXPLICIT param of [fn] is recoverable from the
   explicit arguments. Anything else silently registers nothing — folding is
   display-only and conservative. *)
let register_fold ~(fn : string) ~(is_elim_head : string -> bool) (tm : Core.term) : unit =
  let rec peel acc = function
    | Core.Lambda { bound; implicit; _ } -> peel (implicit :: acc) bound
    | Core.TypedLambda ({ implicit; _ }, body) -> peel (implicit :: acc) body
    | t -> List.rev acc, t
  in
  let params_implicit, body = peel [] tm in
  let k = List.length params_implicit in
  let rec collect t acc =
    match t with
    | Core.App (f, a, implicit) -> collect f ((a, implicit) :: acc)
    | _ -> t, acc
  in
  let head, args = collect body [] in
  match head with
  | Core.Var en when k > 0 && is_elim_head en ->
    let explicit = List.filter (fun (_, implicit) -> not implicit) args in
    let seen = Hashtbl.create 8 in
    let slot_of (a, _) =
      match a with
      | Core.LocalVar ix when ix < k && not (Hashtbl.mem seen ix) ->
        Hashtbl.replace seen ix ();
        Some (F_param (k - 1 - ix))
      | a when is_closed a -> Some (F_closed (erase_names a))
      | _ -> None
    in
    let slots = List.map slot_of explicit in
    if List.exists Option.is_none slots
    then ()
    else begin
      let slots = List.filter_map Fun.id slots in
      let bound_params =
        List.filter_map
          (function
            | F_param i -> Some i
            | F_closed _ -> None)
          slots
      in
      let display =
        List.mapi (fun i implicit -> i, implicit) params_implicit
        |> List.filter_map (fun (i, implicit) -> if implicit then None else Some i)
      in
      (* every explicit param must be recoverable from the explicit spine *)
      if List.for_all (fun i -> List.mem i bound_params) display
      then begin
        let entry = { f_name = fn; f_slots = slots; f_display = display } in
        let existing = Option.value (Hashtbl.find_opt fold_registry en) ~default:[] in
        (* re-elaboration (LSP rechecks, tests) must not duplicate entries *)
        if not (List.mem entry existing)
        then Hashtbl.replace fold_registry en (existing @ [ entry ])
      end
    end
  | _ -> ()
;;

(* Fold a stuck eliminator spine back to `f args…`. [ops] enables operator
   notation on the folded head (`add a b` → `a + b`); the verbose copy passes
   None so it folds without sugaring. *)
let try_fold
      ~(ops : table option)
      ~(pp_arg : Core.term -> string)
      (head : string)
      (explicit_args : Core.term list)
  : string option
  =
  match Hashtbl.find_opt fold_registry head with
  | None -> None
  | Some entries ->
    let n_args = List.length explicit_args in
    let rec try_each = function
      | [] -> None
      | e :: rest ->
        if List.length e.f_slots <> n_args
        then try_each rest
        else begin
          let bindings = Hashtbl.create 8 in
          let matches =
            List.for_all2
              (fun slot arg ->
                 match slot with
                 | F_closed c -> erase_names arg = c
                 | F_param i ->
                   Hashtbl.replace bindings i arg;
                   true)
              e.f_slots
              explicit_args
          in
          if not matches
          then try_each rest
          else (
            let dargs = List.filter_map (Hashtbl.find_opt bindings) e.f_display in
            if List.length dargs <> List.length e.f_display
            then try_each rest
            else (
              let op_result =
                match ops with
                | Some tbl -> try_op tbl ~pp_arg e.f_name dargs
                | None -> None
              in
              match op_result with
              | Some s -> Some s
              | None ->
                (match dargs with
                 | [] -> Some e.f_name
                 | _ -> Some (e.f_name ^ " " ^ String.concat " " (List.map pp_arg dargs)))))
        end
    in
    try_each entries
;;

(* Term-side hook: operator notation first, then eliminator-spine folding. *)
let term_hook (ops : table option) : Core.term Pretty.notation_hook =
  fun ~pp_arg ~head ~explicit_args ->
  let op_result =
    match ops with
    | Some tbl -> try_op tbl ~pp_arg head explicit_args
    | None -> None
  in
  match op_result with
  | Some s -> Some s
  | None -> try_fold ~ops ~pp_arg head explicit_args
;;

(* Value-side hook: operator notation only (folding matches on quoted terms;
   nearly every display site quotes to a term before printing). *)
let value_hook (tbl : table) : Core.value Pretty.notation_hook =
  fun ~pp_arg ~head ~explicit_args -> try_op tbl ~pp_arg head explicit_args
;;

let with_verbose ~(raw : string) ~(sugared : string) : string =
  if String.equal sugared raw then raw else sugared ^ " (i.e. " ^ raw ^ ")"
;;

let pp_term (cv : Context_view.t) (t : Core.term) : string =
  match current_table () with
  | None -> Pretty.pp_term cv t
  | Some tbl ->
    (* the verbose copy folds eliminator spines but skips operator sugar, so
       the raw `Nat/elim …` form never reaches the user *)
    let raw = Pretty.pp_term ~notation:(term_hook None) cv t in
    with_verbose ~raw ~sugared:(Pretty.pp_term ~notation:(term_hook (Some tbl)) cv t)
;;

let pp_value (cv : Context_view.t) (v : Core.value) : string =
  let raw = Pretty.pp_value cv v in
  match current_table () with
  | None -> raw
  | Some tbl ->
    with_verbose ~raw ~sugared:(Pretty.pp_value ~notation:(value_hook tbl) cv v)
;;

(* --- tests ---------------------------------------------------------------- *)

let d = Surface.Mk.d
let mk_app f x = d (Surface.App (false, f, x))
let mk_var n = d (Surface.Var [ n ])

let test_table () =
  let body = mk_app (mk_app (mk_var "Id") (mk_var "x")) (mk_var "y") in
  let decl = Op_resolver.make_op_decl ~template:"\\x = \\y" ~body ~options:[] in
  table_of_ops (Op_resolver.add_decl decl Op_resolver.empty_table)
;;

let id_term a b = Core.App (Core.App (Core.Var "Id", a, false), b, false)

let%expect_test "pp_term: sugared with trailing verbose copy" =
  let t = id_term (Core.Var "a") (Core.Var "b") in
  R.run ~env:(test_table ()) (fun () -> print_string (pp_term Context_view.empty t));
  [%expect {| a = b (i.e. Id a b) |}]
;;

let%expect_test "pp_term: nested sugaring parenthesizes, single verbose copy" =
  let t = id_term (id_term (Core.Var "a") (Core.Var "b")) (Core.Var "c") in
  R.run ~env:(test_table ()) (fun () -> print_string (pp_term Context_view.empty t));
  [%expect {| (a = b) = c (i.e. Id (Id a b) c) |}]
;;

let%expect_test "pp_term: no verbose suffix when nothing sugared" =
  let t = Core.App (Core.Var "f", Core.Var "a", false) in
  R.run ~env:(test_table ()) (fun () -> print_string (pp_term Context_view.empty t));
  [%expect {| f a |}]
;;

let%expect_test "pp_term: arity mismatch prints raw" =
  let t = Core.App (Core.Var "Id", Core.Var "a", false) in
  R.run ~env:(test_table ()) (fun () -> print_string (pp_term Context_view.empty t));
  [%expect {| Id a |}]
;;

let%expect_test "pp_term: no handler degrades to raw" =
  let t = id_term (Core.Var "a") (Core.Var "b") in
  print_string (pp_term Context_view.empty t);
  [%expect {| Id a b |}]
;;

let%expect_test "pp_term: qualified op head sugars bare constructor names" =
  (* ctor values print bare (`prepend`, not `Prog/prepend`) — the alias key
     makes `\i ⍮ \p => Prog/prepend i p` fire on them *)
  let tbl () =
    let body =
      mk_app (mk_app (d (Surface.Var [ "Prog"; "prepend" ])) (mk_var "i")) (mk_var "p")
    in
    let decl = Op_resolver.make_op_decl ~template:"\\i ⍮ \\p" ~body ~options:[] in
    table_of_ops (Op_resolver.add_decl decl Op_resolver.empty_table)
  in
  let t =
    Core.App (Core.App (Core.Var "prepend", Core.Var "ADD", false), Core.Var "rest", false)
  in
  R.run ~env:(tbl ()) (fun () -> print_string (pp_term Context_view.empty t));
  [%expect {| ADD ⍮ rest (i.e. prepend ADD rest) |}]
;;

let%expect_test "pp_term: ambiguous bare segment gets no alias" =
  (* both ◅ and ◁ end in `cons`: bare `cons` must stay raw *)
  let tbl () =
    let mk t path =
      Op_resolver.make_op_decl
        ~template:t
        ~body:(mk_app (mk_app (d (Surface.Var path)) (mk_var "x")) (mk_var "y"))
        ~options:[]
    in
    table_of_ops
      (Op_resolver.add_decl
         (mk "\\x ◁ \\y" [ "Stack"; "cons" ])
         (Op_resolver.add_decl
            (mk "\\x ◅ \\y" [ "StackShape"; "cons" ])
            Op_resolver.empty_table))
  in
  let t =
    Core.App (Core.App (Core.Var "cons", Core.Var "a", false), Core.Var "b", false)
  in
  R.run ~env:(tbl ()) (fun () -> print_string (pp_term Context_view.empty t));
  [%expect {| cons a b |}]
;;

(* --- folding tests -------------------------------------------------------- *)

let app f a = Core.App (f, a, false)

(* fun m n => Nat/elim m M Z S n — the compiled shape of
   `\let add (m n : Nat) : Nat \where add m n <= \elim m` with closed
   motive/cases (abbreviated to plain Vars here). *)
let add_compiled =
  Core.Lambda
    { name = Named "m"
    ; implicit = false
    ; bound =
        Core.Lambda
          { name = Named "n"
          ; implicit = false
          ; bound =
              app
                (app
                   (app
                      (app (app (Core.Var "Nat/elim") (Core.LocalVar 1)) (Core.Var "M"))
                      (Core.Var "Z"))
                   (Core.Var "S"))
                (Core.LocalVar 0)
          }
    }
;;

let plus_table () =
  let decl =
    Op_resolver.make_op_decl ~template:"\\x + \\y" ~body:(mk_var "add") ~options:[]
  in
  table_of_ops (Op_resolver.add_decl decl Op_resolver.empty_table)
;;

let stuck_spine a b =
  app
    (app
       (app (app (app (Core.Var "Nat/elim") a) (Core.Var "M")) (Core.Var "Z"))
       (Core.Var "S"))
    b
;;

let%expect_test "fold: stuck elim spine folds to function name and sugars" =
  Hashtbl.reset fold_registry;
  register_fold ~fn:"add" ~is_elim_head:(String.equal "Nat/elim") add_compiled;
  let t = stuck_spine (Core.Var "a") (Core.Var "b") in
  R.run ~env:(plus_table ()) (fun () -> print_string (pp_term Context_view.empty t));
  [%expect {| a + b (i.e. add a b) |}]
;;

let%expect_test "fold: verbose copy folds without operator sugar" =
  Hashtbl.reset fold_registry;
  register_fold ~fn:"add" ~is_elim_head:(String.equal "Nat/elim") add_compiled;
  (* no operator declared for add: folded display only, no suffix needed *)
  let t = stuck_spine (Core.Var "a") (Core.Var "b") in
  R.run ~env:(table_of_ops Op_resolver.empty_table) (fun () ->
    print_string (pp_term Context_view.empty t));
  [%expect {| add a b |}]
;;

let%expect_test "fold: mismatched closed slot prints the raw spine" =
  Hashtbl.reset fold_registry;
  register_fold ~fn:"add" ~is_elim_head:(String.equal "Nat/elim") add_compiled;
  let t =
    app
      (app
         (app
            (app (app (Core.Var "Nat/elim") (Core.Var "a")) (Core.Var "OTHER"))
            (Core.Var "Z"))
         (Core.Var "S"))
      (Core.Var "b")
  in
  R.run ~env:(table_of_ops Op_resolver.empty_table) (fun () ->
    print_string (pp_term Context_view.empty t));
  [%expect {| Nat/elim a OTHER Z S b |}]
;;

let%expect_test "fold: non-eliminator head registers nothing" =
  Hashtbl.reset fold_registry;
  register_fold ~fn:"inc" ~is_elim_head:(fun _ -> false) add_compiled;
  print_string (string_of_int (Hashtbl.length fold_registry));
  [%expect {| 0 |}]
;;

let%expect_test "fold: nested stuck spines fold recursively inside operators" =
  Hashtbl.reset fold_registry;
  register_fold ~fn:"add" ~is_elim_head:(String.equal "Nat/elim") add_compiled;
  (* Id (suc (add n m)) (add n (suc m)) — the motivating example *)
  let suc x = app (Core.Var "suc") x in
  let t =
    id_term
      (suc (stuck_spine (Core.Var "n") (Core.Var "m")))
      (stuck_spine (Core.Var "n") (suc (Core.Var "m")))
  in
  let tbl () =
    let eq =
      Op_resolver.make_op_decl
        ~template:"\\x = \\y"
        ~body:(mk_app (mk_app (mk_var "Id") (mk_var "x")) (mk_var "y"))
        ~options:[]
    in
    let plus =
      Op_resolver.make_op_decl ~template:"\\x + \\y" ~body:(mk_var "add") ~options:[]
    in
    table_of_ops
      (Op_resolver.add_decl plus (Op_resolver.add_decl eq Op_resolver.empty_table))
  in
  R.run ~env:(tbl ()) (fun () -> print_string (pp_term Context_view.empty t));
  [%expect {| (suc (n + m)) = (n + (suc m)) (i.e. Id (suc (add n m)) (add n (suc m))) |}]
;;
