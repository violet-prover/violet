(* Elaboration helpers specific to inductive type declarations and
   elim-definitions. The remaining inductive/elim logic in elab.ml
   (KTopData_HaveType, KTopElimDef_HaveType, bind_constructor) delegates
   to the functions below. *)

open Violet_kernel.Syntax

(* Wrap a constructor's user-written type with implicit Π over the inductive
   type's params, so the stored global type is self-contained and so the
   params are in scope while checking the user's constructor type. *)
val close_ctor_type : Surface.pretype binder list -> Surface.pretype -> Surface.pretype

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

val build_owner_map : ind_head:string -> Context.ind_info -> (string * string) list

val readback_value_to_surface
  :  loc:Asai.Range.t
  -> user_level_names:(int * string) list
  -> owner_map:(string * string) list
  -> Violet_kernel.Syntax.Core.value
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
