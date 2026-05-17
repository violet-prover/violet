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

(* Build a Surface preterm body for an Elim_def. *)
val build_elim_body
  :  loc:Asai.Range.t
  -> func_name:string
  -> params:Surface.pretype binder list
  -> signature:Surface.pretype
  -> opens:string list
  -> intros:(string * bool) list
  -> target:string
  -> clauses:Surface.clause list
  -> Surface.preterm
