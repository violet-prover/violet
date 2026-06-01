type binder_name = Violet_kernel.Syntax.binder_name =
  | Named of string
  | Anon
[@@deriving show]

type 't binder = 't Violet_kernel.Syntax.binder =
  { name : binder_name
  ; bound : 't
  ; implicit : bool
  }
[@@deriving show]

module Name = Violet_kernel.Syntax.Name

type preterm =
  | Located of preterm Asai.Range.located
  | Universe
  | Hole
  | Goal of string option
  | Var of string list
  | App of bool * preterm * preterm
  | Lambda of preterm binder
  | TypedLambda of pretype binder * preterm
  | Pi of pretype binder * pretype
  | Max of preterm * preterm
  | Op_soup of soup_item list
  | RecordLit of (string * preterm) list
  | RecordUpdate of preterm * (string * preterm) list
  | Proj of preterm * string
  | IdAbsurd of preterm
  | Absurd of preterm
  | Inline_elim of inline_elim_data
[@@deriving show]

and inline_elim_data =
  { target : string
  ; siblings : (clause * pattern list) list
  ; outer_subst : (int * Violet_kernel.Syntax.Core.value) list
  ; target_override : preterm option
  }

and soup_item =
  | SI_Atom of preterm
  | SI_Name of string * Asai.Range.t option
  | SI_Imp_arg of preterm
[@@deriving show]

and pretype = preterm

and pattern =
  | PVar of string
  | PWildcard
  | PCon of string * pattern list
  | PImpVar of string
  | PRecord of (string * pattern) list

and clause =
  { head : string
  ; patterns : pattern list
  ; body : preterm
  }
[@@deriving show]

type as_arg =
  { term : preterm
  ; implicit : bool
  }

type stack_move =
  | Intro
  | Split
[@@deriving show]

type op_name_path = string list [@@deriving show]

type op_assoc =
  | OA_Left
  | OA_Right
  | OA_None
[@@deriving show]

type op_option =
  | OO_Weaker_than of op_name_path list
  | OO_Stronger_than of op_name_path list
  | OO_Same_as of op_name_path list
  | OO_Associativity of op_assoc
[@@deriving show]

type top =
  | Let of
      { name : string
      ; name_loc : Asai.Range.t option
      ; bindings : pretype binder list
      ; result_ty : pretype
      ; body : preterm
      }
  | Data of
      { name : string
      ; name_loc : Asai.Range.t option
      ; params : pretype binder list
      ; deps : pretype binder list
      ; ind_ty : pretype
      ; ind_ty_loc : Asai.Range.t option
      ; ctors : pretype binder list
      ; ctor_name_locs : Asai.Range.t option list
      }
  | Universe_decl of (string * Asai.Range.t option) list
  | Stack_def of
      { name : string
      ; name_loc : Asai.Range.t option
      ; params : pretype binder list
      ; signature : pretype
      ; moves : stack_move list
      ; clauses : clause list
      }
  | Elim_def of
      { name : string
      ; name_loc : Asai.Range.t option
      ; params : pretype binder list
      ; signature : pretype
      ; opens : string list
      ; intros : (string * bool) list
      ; target : string
      ; clauses : clause list
      }
  | Operator_decl of
      { template : string
      ; body : preterm
      ; options : op_option list
      }
  | Record of
      { name : string
      ; name_loc : Asai.Range.t option
      ; params : pretype binder list
      ; ind_ty : pretype
      ; fields : pretype binder list
      }
[@@deriving show]

type t =
  { name : string
  ; imports : Yuujinchou.Trie.path list
  ; exports : (string * Asai.Range.t option) list
  ; tops : top Asai.Range.located list
  }

val lambda : string list -> preterm -> preterm
val typed_lambda : pretype binder list -> preterm -> preterm
val telescope : pretype -> pretype binder list
val codomain : pretype -> pretype
val codomain_loc : pretype -> Asai.Range.t option
val pi : pretype binder list -> pretype -> pretype
val applied_spine : preterm -> preterm list
val apply : preterm -> preterm list -> preterm
val apply_tele : preterm -> preterm binder list -> preterm
