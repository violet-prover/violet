open Syntax.Core
open Bwd

let count = ref 0

let fresh (vars : string bwd) : term =
  let r = InsertedMeta (MetaVar !count, vars) in
  count := !count + 1;
  r

module PartialRenaming = struct
  type t = {
    domain : string bwd;
    codomain : string bwd;
    rename : (string, string) Hashtbl.t;
  }

  let invert (domain : string bwd) (sp : value bwd) : t =
    let rec go = function
      | Emp -> Hashtbl.create ~random:true 1000
      | Snoc (rest, (t, v)) -> (
          let ren = go rest in
          match Evaluation.force t with
          | Rigid (x, Emp) -> (
              match Hashtbl.find_opt ren x with
              | Some _ -> Reporter.fatalf Elab_error "bad"
              | None ->
                  Hashtbl.add ren x v;
                  ren)
          | _ -> Reporter.fatalf Elab_error "invert failed")
    in
    { domain; codomain = domain; rename = go @@ Bwd.combine sp domain }

  let rec rename (m : metavar) (renaming : t) (rhs : value) : term =
    match rhs with
    | Universe -> Universe
    | Flex (m', sp) ->
        if m = m' then
          Reporter.fatalf Elab_error "meta variable %s itself occurs in rhs"
            ([%show: metavar] m)
        else rename_sp m renaming (Meta m') sp
    | Rigid (x, sp) -> (
        match Hashtbl.find_opt renaming.rename x with
        | None -> Reporter.fatalf Elab_error "cannot complete partial renaming"
        | Some x' -> rename_sp m renaming (Var x') sp)
    | VLambda { implicit; name; bound = clos } ->
        Lambda
          {
            implicit;
            name;
            bound = rename m renaming (clos @@ Rigid (name, Emp));
          }
    | VPi ({ implicit; name; bound = a }, b) ->
        Pi
          ( { implicit; name; bound = rename m renaming a },
            rename m renaming (b (Rigid (name, Emp))) )

  and rename_sp (m : metavar) (renaming : t) (t : term) (sp : value bwd) : term
      =
    match sp with
    | Emp -> t
    | Snoc (sp, u) -> App (rename_sp m renaming t sp, rename m renaming u)

  let rec lams (dom : string list) (tm : term) : term =
    match dom with
    | [] -> tm
    | name :: dom -> Lambda { name; bound = lams dom tm; implicit = false }

  let run m sp rhs =
    let dom = Bwd.map (fun _ -> Format.sprintf "<%d>" (Random.int 1000)) sp in
    let renaming = invert dom sp in
    let rhs = rename m renaming rhs in
    let solution = lams (Bwd.to_list dom) rhs in
    Reporter.tracef "solution is: %s" ([%show: term] solution) @@ fun () ->
    Evaluation.eval solution
end

let solve (m : metavar) (sp : value bwd) (rhs : value) : unit =
  let spine_str = String.concat " " @@ List.map (fun v -> [%show: value] v) (Bwd.to_list sp) in
  Reporter.tracef "spine: %s" spine_str @@ fun () ->

  let solution = PartialRenaming.run m sp rhs in
  Evaluation.insert_meta m solution
