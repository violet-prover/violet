type binder_name =
  | Named of string
  | Anon
[@@deriving show]

module Name : sig
  type t = binder_name =
    | Named of string
    | Anon

  val to_string : t -> string
end

type 't binder =
  { name : binder_name
  ; bound : 't
  ; implicit : bool
  }
[@@deriving show]

module Core : sig
  type metavar = MetaVar of int [@@deriving show]

  type term =
    | Universe of Level.level
    | LocalVar of int
    | Var of string
    | App of term * term
    | Lambda of term binder
    | TypedLambda of typ binder * term
    | Pi of typ binder * typ
    | Meta of metavar
    | InsertedMeta of metavar * int
    | Lift of
        { from_lvl : Level.level
        ; to_lvl : Level.level
        ; ty : term
        }
    | LiftTerm of
        { from_lvl : Level.level
        ; to_lvl : Level.level
        ; ty : term
        ; tm : term
        }
    | UnliftTerm of
        { from_lvl : Level.level
        ; to_lvl : Level.level
        ; ty : term
        ; tm : term
        }
    | RecordType of
        { name : string
        ; params : term list
        ; fields : typ binder list
        }
    | RecordIntro of
        { name : string
        ; fields : (string * term) list
        }
    | RecordProj of
        { record : term
        ; field : string
        }
    | IdAbsurd of term
  [@@deriving show]

  and typ = term [@@deriving show]

  type value =
    | Flex of metavar * value Bwd.bwd
    | RigidLocal of int * value Bwd.bwd
    | Var of string * value Bwd.bwd
    | IndType of string * value Bwd.bwd
    | Label of string * value Bwd.bwd
    | Elim of elim_head * value Bwd.bwd
    | VLambda of (value -> value) binder
    | VPi of value_ty binder * (value -> value)
    | Universe of Level.level
    | VLift of
        { from_lvl : Level.level
        ; to_lvl : Level.level
        ; ty : value
        }
    | VLiftTerm of
        { from_lvl : Level.level
        ; to_lvl : Level.level
        ; ty : value
        ; tm : value
        }
    | VUnliftTerm of
        { from_lvl : Level.level
        ; to_lvl : Level.level
        ; ty : value
        ; tm : value
        }
    | VRecordType of
        { name : string
        ; params : value list
        ; fields : value_ty binder list
        ; field_env : value Bwd.bwd
        ; field_terms : typ binder list
        }
    | VRecordIntro of
        { name : string
        ; fields : (string * value) list
        }
    | VRecordProj of value * string * value Bwd.bwd
    | VIdAbsurd of value
  [@@deriving show]

  and elim_head =
    { elim_name : string
    ; reducer : value Bwd.bwd -> value option
    }

  and value_ty = value

  val rigid_local : int -> value
  val lvl_to_ix : env_size:int -> int -> int
end
