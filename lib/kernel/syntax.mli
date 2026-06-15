type binder_name =
  | Named of string
  | Anon
[@@deriving show]

module Name : sig
  type t = binder_name =
    | Named of string
    | Anon

  val to_string : t -> string

  (* Qualified global names are segment paths joined by `/` (e.g. `std/Nat/suc`) *)
  val of_segments : string list -> string
  val to_segments : string -> string list
  val qualify : string -> string -> string
end

type 't binder =
  { name : binder_name
  ; bound : 't
  ; implicit : bool
  }
[@@deriving show]

module Core : sig
  type metavar = MetaVar of int

  type term =
    | Universe of Level.level
    | LocalVar of int
    | Var of string
    | App of term * term * bool
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
    | Empty
    | Absurd of term

  and typ = term

  type value =
    | Flex of metavar * spine
    | RigidLocal of int * spine
    | Var of string * spine
    | IndType of string * spine
    | Label of string * spine
    | Elim of elim_head * spine
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
    | VRecordProj of value * string * spine
    | VIdAbsurd of value
    | VEmpty
    | VAbsurd of value * spine

  and elim_head =
    { elim_name : string
    ; reducer : spine -> value option
    }

  and value_ty = value

  and arg =
    { tm : value
    ; implicit : bool
    }

  and spine = arg Bwd.bwd

  val rigid_local : int -> value
  val lvl_to_ix : env_size:int -> int -> int
  val explicit_arg : value -> arg
  val implicit_arg : value -> arg
  val spine_values : spine -> value Bwd.bwd
end
