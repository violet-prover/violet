open Syntax.Core
open Bwd

let count = ref 0

let fresh (vars : string bwd) : term =
  let r = InsertedMeta (MetaVar !count, vars) in
  count := !count + 1;
  r
;;

let meta_context = Hashtbl.create ~random:true 100
let lookup_meta (mvar : metavar) : value option = Hashtbl.find_opt meta_context mvar

let insert_meta (mvar : metavar) (solution : value) : unit =
  Hashtbl.add meta_context mvar solution
;;

let eval (mvar : metavar) : value =
  match lookup_meta mvar with
  | Some t -> t
  | None -> Flex (mvar, Emp)
;;

module GlobalDefs = Set.Make (String)

module Defs = struct
  type t = GlobalDefs.t
end

(* GlobalState tracks name of global definitions,
  this helps we understand if a name is already bound when we are solving metas
*)
module GlobalState = Algaeff.State.Make (Defs)

module Bound = struct
  type t = string bwd
end

module BoundState = Algaeff.State.Make (Bound)

let meta_fresh () =
  let globals = Bwd.of_list @@ List.rev @@ GlobalDefs.elements (GlobalState.get ()) in
  let locals = BoundState.get () in
  if Bwd.is_empty locals then fresh globals else fresh locals
;;
