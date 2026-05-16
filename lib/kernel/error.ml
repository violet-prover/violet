open Syntax

type kernel_error =
  | UnboundLocal of int
  | UnboundGlobal of string
  | OrphanMeta of Core.metavar
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
  | BadApplication of Core.value
  | BadProjection of
      { value : Core.value
      ; field : string
      }
  | LocalVarOutOfRange of
      { index : int
      ; env_size : int
      }
[@@deriving show]

exception Kernel_error of kernel_error
