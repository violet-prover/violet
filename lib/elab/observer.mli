type event =
  | Def of
      { path : string list
      ; loc : Asai.Range.t
      ; name_loc : Asai.Range.t option
      ; ty : Violet_kernel.Syntax.Core.value_ty
      ; pp_ty : string
      }
  | Use of
      { path : string list
      ; loc : Asai.Range.t
      ; def_loc : Asai.Range.t option
      ; ty : Violet_kernel.Syntax.Core.value_ty
      ; pp_ty : string
      }
  | Goal of
      { path : string list
      ; loc : Asai.Range.t
      ; ty : Violet_kernel.Syntax.Core.value_ty
      ; ctx : (string * string) list
      ; pp_target : string
      }
  | Binder of
      { path : string list
      ; loc : Asai.Range.t
      }

val emit : event -> unit
val run : on_event:(event -> unit) -> (unit -> 'a) -> 'a
val run_silent : (unit -> 'a) -> 'a
