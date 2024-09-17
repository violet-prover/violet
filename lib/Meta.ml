open Syntax.Core
open Bwd

let count = ref 0
let fresh () : term =
  let r = Meta (MetaVar !count) in
  count := !count + 1;
  r

module PartialRenaming = struct
  type t = { domain : string bwd; codomain : string bwd; rename : (string, string) Hashtbl.t }

  let invert (codomain : string bwd) (sp : value bwd) : t =
    let domain = Bwd.map (fun _ -> (Format.sprintf "<@%d>" (Random.int 1000))) sp in
    let rec go = function
      | Emp -> Hashtbl.create ~random:true 1000
      | Snoc (rest, (t, v)) ->
          let ren = go rest in
          match Evaluation.force t with
          | Rigid (x, Emp) ->
            (match Hashtbl.find_opt ren x with
            | Some _ -> Reporter.fatalf Elab_error "bad"
            | None -> Hashtbl.add ren x v; ren)            
          | _ ->
            Reporter.fatalf Elab_error "invert failed"
    in
    { domain; codomain; rename=go @@ Bwd.combine sp domain }
  
  let rec rename (m : metavar) (renaming : t) (rhs : value) : term =
    match rhs with
    | Universe -> Universe
    | Flex (m', sp) ->
      if m = m' then
        Reporter.fatalf Elab_error "%s occurs in rhs" ([%show: metavar] m)
      else
        rename_sp m renaming (Meta m') sp
    | Rigid (x, sp) ->
      (match Hashtbl.find_opt renaming.rename x with
      | None -> Reporter.fatalf Elab_error "cannot complete partial renaming"
      | Some x' -> rename_sp m renaming (Var x') sp)
    | VLambda (t) ->
      Lambda {name="<x>"; bound=rename m renaming (t @@ (Rigid ((Bwd.nth renaming.codomain 1), Emp))); implicit=false}
    | VPi ({name;bound=a;implicit}, b) ->
      Pi
        ({name; bound=(rename m renaming a); implicit},
        (rename m renaming (b (Rigid ((Bwd.nth renaming.codomain 1), Emp)))))
  and rename_sp (m : metavar) (renaming : t) (t : term) (sp : value bwd) : term =
    match sp with
    | Emp -> t
    | Snoc (sp, u) -> App ((rename_sp m renaming t sp), (rename m renaming u))

  let rec lams (dom : string bwd) (tm : term) : term =
    match dom with
    | Emp -> tm
    | Snoc (dom,name) -> Lambda { name; bound =lams dom tm ; implicit = false }

  let run m sp rhs =
    let dom = Bwd.map (fun _ -> (Format.sprintf "<!%d>" (Random.int 1000))) sp in
    let renaming = invert dom sp in
    let rhs  = rename m renaming rhs in
    Eio.traceln "solution: %s" ([%show: term] rhs);
    let solution = Evaluation.eval @@ lams dom rhs in
    solution
end

let solve (m : metavar) (sp : value bwd) (rhs : value) : unit =
  Eio.traceln "spine:";
  Bwd.iter (fun v -> Eio.traceln "%s" ([%show: value] v)) sp;

  let solution = PartialRenaming.run m sp rhs in
  Evaluation.insert_meta m solution
