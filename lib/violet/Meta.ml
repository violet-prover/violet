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
