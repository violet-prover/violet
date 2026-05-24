module Syntax = Violet_kernel.Syntax
module Level = Violet_kernel.Level
module Context_view = Violet_kernel.Context_view
module Pretty = Violet_kernel.Pretty
module Evaluation = Wiring.Eval
module Check = Wiring.Check
module Unification = Unify
open Syntax
open Surface_utils

(* These run a single GInfer against an existing handler state
   (Context.S / Env.S already populated by prior `check_module` calls).
   The caller is responsible for entering the right `Context.S.section` /
   `Env.S.section` and re-applying any visible-namespace imports so that the
   expression sees the names it expects. *)

let infer_expression ~(module_name : string) (p : Surface.preterm)
  : Core.term * Core.value
  =
  let open Elab in
  let loc =
    match loc_of p with
    | Some l -> l
    | None -> Asai.Range.of_lex_range (Lexing.dummy_pos, Lexing.dummy_pos)
  in
  let m =
    make_machine
      ~module_name
      ~kernel_module:(Violet_kernel.Module.create ())
      ~goal_counter:(ref 0)
      ()
  in
  push m (GInfer (loc, p));
  match drive m with
  | PTermType (tm, ty) -> tm, ty
  | other ->
    Reporter.fatalf ~loc Elab_error "infer_expression: got %s" ([%show: produced] other)
;;

(* User-facing pretty-printer for REPL output. The empty local context is fine
   because expressions in the REPL don't introduce free locals *)
let pretty_repl_value (v : Core.value) : string =
  Pretty.pp_term Context_view.empty (Evaluation.quote 0 v)
;;
