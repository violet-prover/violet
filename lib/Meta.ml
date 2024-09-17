open Syntax.Core
open Bwd

let count = ref 0
let fresh () : term =
  let r = Meta (MetaVar !count) in
  count := !count + 1;
  r

type meta_res =
  | Solved of value
  | Unsolved

let lookupMeta (_mvar : metavar) : meta_res =
  Unsolved

let eval (mvar : metavar) : value =
  match lookupMeta mvar with
  | Solved t -> t
  | Unsolved -> Flex (mvar, Emp)

let solve (m : metavar) (_sp : value bwd) (t : value) : unit =
  Eio.traceln "%s ?= %s" ([%show: metavar] m) ([%show: value] t);
  ()
