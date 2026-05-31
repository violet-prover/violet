open Syntax

type kernel_error =
  | UnboundLocal of int
  | UnboundGlobal of string
  | OrphanMeta of
      (Core.metavar
      [@printer fun fmt m -> Format.pp_print_string fmt (Pretty.pp_metavar m)])
  | NonStrictlyPositive of
      { data : string
      ; ctor : string
      ; reason : string
      }
  | DuplicateDecl of string
  | UniverseMismatch of
      { lhs : Level.level
      ; rhs : Level.level
      }
  | BadApplication of
      (Core.value
      [@printer
        fun fmt v -> Format.pp_print_string fmt (Pretty.pp_value Context_view.empty v)])
  | BadProjection of
      { value : Core.value
            [@printer
              fun fmt v ->
                Format.pp_print_string fmt (Pretty.pp_value Context_view.empty v)]
      ; field : string
      }
  | LocalVarOutOfRange of
      { index : int
      ; env_size : int
      }
[@@deriving show]

exception Kernel_error of kernel_error
