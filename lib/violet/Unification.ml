open Syntax
open Bwd
open Evaluation

module PartialRenaming = struct
  open Core

  type t = (string, string) Hashtbl.t

  let invert (domain : string bwd) (sp : value bwd) : t =
    let rec go = function
      | Emp -> Hashtbl.create ~random:true 1000
      | Snoc (rest, (t, v)) ->
        let ren = go rest in
        (match force t with
         | Rigid (x, Emp) ->
           (match Hashtbl.find_opt ren x with
            | Some _ -> Reporter.fatalf Elab_error "bad"
            | None ->
              Hashtbl.add ren x v;
              ren)
         | _ -> Reporter.fatalf Elab_error "invert failed")
    in
    go @@ Bwd.combine sp domain
  ;;

  let rec rename (m : metavar) (renaming_map : t) (rhs : value) : term =
    match rhs with
    | Universe -> Universe
    | Flex (m', sp) ->
      if m = m'
      then
        Reporter.fatalf
          Elab_error
          "meta variable %s itself occurs in rhs"
          ([%show: metavar] m)
      else rename_sp m renaming_map (Meta m') sp
    | Rigid (x, sp) ->
      (match Hashtbl.find_opt renaming_map x with
       | None ->
         if Context.has x
         then (
           let ts = Bwd.map (fun x -> rename m renaming_map x) sp in
           List.fold_left (fun acc k -> App (acc, k)) (Var x) @@ Bwd.to_list ts)
         else
           Reporter.fatalf
             Elab_error
             "cannot complete partial renaming, there has no variable %s in context"
             x
       | Some x' -> rename_sp m renaming_map (Var x') sp)
      (* 把 constructor 這些東西 quote 回 variable 也沒差，還是會執行成 label *)
    | Label (x, sp) -> rename_sp m renaming_map (Var x) sp
    | VLambda { implicit; name; bound = clos } ->
      Lambda { implicit; name; bound = rename m renaming_map (clos @@ Rigid (name, Emp)) }
    | VPi ({ implicit; name; bound = a }, b) ->
      Pi
        ( { implicit; name; bound = rename m renaming_map a }
        , rename m renaming_map (b (Rigid (name, Emp))) )

  and rename_sp (m : metavar) (renaming : t) (t : term) (sp : value bwd) : term =
    match sp with
    | Emp -> t
    | Snoc (sp, u) -> App (rename_sp m renaming t sp, rename m renaming u)
  ;;

  let rec lams (dom : string list) (tm : term) : term =
    match dom with
    | [] -> tm
    | name :: dom -> Lambda { name; bound = lams dom tm; implicit = false }
  ;;

  let run m sp rhs =
    let dom = Bwd.map (fun _ -> Format.sprintf "<%d>" (Random.int 1000)) sp in
    let renaming_map = invert dom sp in
    let rhs = rename m renaming_map rhs in
    let solution = lams (Bwd.to_list dom) rhs in
    Reporter.tracef "solution is: %s" ([%show: term] solution) @@ fun () -> eval solution
  ;;
end

let solve (m : Core.metavar) (sp : Core.value bwd) (rhs : Core.value) : unit =
  let spine_str =
    String.concat " <: " @@ List.map (fun v -> [%show: Core.value] v) (Bwd.to_list sp)
  in
  Reporter.tracef "spine: %s" spine_str
  @@ fun () ->
  let solution = PartialRenaming.run m sp rhs in
  Meta.insert_meta m solution
;;

let count = ref 0

let fresh_variable () : Core.value =
  let r = Format.sprintf "*%d" !count in
  count := !count + 1;
  Rigid (r, Emp)
;;

let rec unify ~loc (a : Core.value) (b : Core.value) : unit =
  Reporter.tracef
    ~loc
    "unify `%s` and `%s` (or verbose `%s ?= %s`)"
    ([%show: Core.value] a)
    ([%show: Core.value] b)
    ([%show: Core.value] (force a))
    ([%show: Core.value] (force b))
  @@ fun () ->
  match force a, force b with
  | Universe, Universe -> ()
  | Rigid (h1, sp1), Rigid (h2, sp2) when String.equal h1 h2 -> unify_spine ~loc sp1 sp2
  | Label (h1, sp1), Label (h2, sp2) when String.equal h1 h2 -> unify_spine ~loc sp1 sp2
  | VLambda { bound = bound1; _ }, VLambda { bound = bound2; _ } ->
    let x = fresh_variable () in
    unify ~loc (bound1 x) (bound2 x)
  | VLambda { bound; _ }, t | t, VLambda { bound; _ } ->
    let x = fresh_variable () in
    unify ~loc (bound x) (vapp t x)
  | VPi (_, b1), VPi (_, b2) ->
    let x = fresh_variable () in
    unify ~loc (b1 x) (b2 x)
  | VPi ({ implicit = true; _ }, b), t | t, VPi ({ implicit = true; _ }, b) ->
    let x = eval @@ Meta.meta_fresh () in
    unify ~loc (b x) t
  | Flex (m1, sp1), Flex (m2, sp2) when m1 = m2 -> unify_spine ~loc sp1 sp2
  | t, Flex (m, sp) | Flex (m, sp), t -> solve m sp t
  | expected, actual ->
    Reporter.fatalf
      ~loc
      Type_error
      "cannot unify `%s ?= %s` (or verbose `%s ?= %s`)"
      ([%show: Core.value] expected)
      ([%show: Core.value] actual)
      ([%show: Core.value] a)
      ([%show: Core.value] b)

and unify_spine ~loc (xs : Core.value bwd) (ys : Core.value bwd) : unit =
  match xs, ys with
  | Emp, Emp -> ()
  | Snoc (xs, x), Snoc (ys, y) ->
    unify_spine ~loc xs ys;
    unify ~loc x y
  | _, _ ->
    let left = String.concat " <: " @@ Bwd.to_list @@ Bwd.map Core.show_value xs in
    let right = String.concat " <: " @@ Bwd.to_list @@ Bwd.map Core.show_value ys in
    Reporter.fatalf
      ~loc
      Elab_error
      "cannot unify spine `%s` and `%s`, spine mismatched"
      left
      right
;;
