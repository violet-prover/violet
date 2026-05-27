(* Elimination synthesis logic for inductive types. Builds surface-level
   eliminator call terms from elim-def clauses. *)

open Violet_surface
open Violet_kernel.Syntax

(* Walk the function's full Pi tower in parallel with the user's intros to
   produce one entry per Pi-binder: `(name, implicit)`. *)
val compute_effective_intros
  :  loc:Asai.Range.t
  -> bindings:Surface.pretype binder list
  -> signature:Surface.pretype
  -> intros:(string * bool) list
  -> (string * bool) list

(* Build a Surface preterm body for an Elim_def.

   `target_type_value` is the Core-evaluated type of the target binder. It is
   used only to drive the new index-unification path (non-variable indices
   in the target's type); for purely variable indices the existing
   renaming-based path is taken and `target_type_value` is unused.

   `start_lvl` is the local context level at the point where the wrapping
   intro-lambdas begin binding. The new path uses it to assign de Bruijn
   levels to user intros and to fresh ctor-field flex binders, consistent
   with what the elaborator will see when it later checks the generated
   term. *)
val build_elim_body
  :  loc:Asai.Range.t
  -> func_name:string
  -> params:Surface.pretype binder list
  -> signature:Surface.pretype
  -> opens:string list
  -> intros:(string * bool) list
  -> target:string
  -> clauses:Surface.clause list
  -> target_type_value:Violet_kernel.Syntax.Core.value
  -> start_lvl:int
  -> Surface.preterm

val build_inline_elim_dispatch
  :  loc:Asai.Range.t
  -> target_name:string
  -> target_type_raw:Violet_kernel.Syntax.Core.value
  -> target_type_value:Violet_kernel.Syntax.Core.value
  -> siblings:(Surface.clause * Surface.pattern list) list
  -> result_type_surface:Surface.preterm
  -> start_lvl:int
  -> user_level_names:(int * string) list
  -> outer_subst:(int * Violet_kernel.Syntax.Core.value) list
  -> target_override:Surface.preterm option
  -> Surface.preterm
