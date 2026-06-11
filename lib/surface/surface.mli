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

type 'a spanned =
  { loc : Asai.Range.t
  ; value : 'a
  }

val pp_spanned
  :  (Format.formatter -> 'a -> unit)
  -> Format.formatter
  -> 'a spanned
  -> unit

val show_spanned : ('a -> string) -> 'a spanned -> string

type preterm =
  (preterm_record[@printer fun fmt t -> fprintf fmt "%s" (show_preterm_node t.node)])

and preterm_record =
  { loc : (Asai.Range.t[@opaque])
  ; node : preterm_node
  }

and preterm_node =
  | Universe
  | Hole
  | Goal of string option
  | Var of string list
  | App of bool * preterm * preterm
  | Lambda of preterm sbinder
  | TypedLambda of pretype sbinder * preterm
  | Pi of pretype sbinder * pretype
  | Max of preterm * preterm
  | Op_soup of soup_item list
  | RecordLit of (string spanned * preterm) list
  | RecordUpdate of preterm * (string spanned * preterm) list
  | Proj of preterm * string spanned
  | IdAbsurd of preterm
  | Absurd of preterm
  | Inline_elim of inline_elim_data

and 't sbinder =
  { name : binder_name spanned
  ; bound : 't
  ; implicit : bool
  }

and inline_elim_data =
  { target : string
  ; siblings : (clause * pattern list) list
  ; outer_subst : (int * Violet_kernel.Syntax.Core.value) list
  ; target_override : preterm option
  }

and soup_item =
  | SI_Atom of preterm
  | SI_Name of string spanned
  | SI_Imp_arg of preterm

and pretype = preterm

and pattern =
  (pattern_record[@printer fun fmt p -> fprintf fmt "%s" (show_pattern_node p.pnode)])

and pattern_record =
  { ploc : (Asai.Range.t[@opaque])
  ; pnode : pattern_node
  }

and pattern_node =
  | PVar of string
  | PWildcard
  | PCon of string spanned * pattern list
  | PImpVar of string
  | PRecord of (string spanned * pattern) list

and clause =
  { head : string spanned
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
      { name : string spanned
      ; bindings : pretype sbinder list
      ; result_ty : pretype
      ; body : preterm
      }
  | Data of
      { name : string spanned
      ; params : pretype sbinder list
      ; deps : pretype sbinder list
      ; ind_ty : pretype
      ; ctors : pretype sbinder list
      }
  | Universe_decl of string spanned list
  | Stack_def of
      { name : string spanned
      ; params : pretype sbinder list
      ; signature : pretype
      ; moves : stack_move list
      ; clauses : clause list
      }
  | Elim_def of
      { name : string spanned
      ; params : pretype sbinder list
      ; signature : pretype
      ; opens : string list
      ; intros : (string spanned * bool) list
      ; target : string spanned
      ; clauses : clause list
      }
  | Operator_decl of
      { template : string
      ; body : preterm
      ; options : op_option list
      }
  | Record of
      { name : string spanned
      ; params : pretype sbinder list
      ; ind_ty : pretype
      ; fields : pretype sbinder list
      }
  | Axiom of
      { name : string spanned
      ; bindings : pretype sbinder list
      ; result_ty : pretype
      }
[@@deriving show]

type t =
  { name : string
  ; imports : Yuujinchou.Trie.path list
  ; exports : string spanned list
  ; tops : top spanned list
  }

val join_loc : Asai.Range.t -> Asai.Range.t -> Asai.Range.t
val dummy_loc : Asai.Range.t

module Mk : sig
  val at : Asai.Range.t -> preterm_node -> preterm
  val re_loc : Asai.Range.t -> preterm -> preterm
  val sn : Asai.Range.t -> 'a -> 'a spanned

  (* Dummy-located constructors, for synthesized terms with no better
     provenance (whitebox tests, REPL, builtin elaboration). *)
  val d : preterm_node -> preterm
  val dn : 'a -> 'a spanned
end

val forget_binder : 't sbinder -> 't Violet_kernel.Syntax.binder
val lambda : string spanned list -> preterm -> preterm
val typed_lambda : pretype sbinder list -> preterm -> preterm
val telescope : pretype -> pretype sbinder list
val codomain : pretype -> pretype
val pi : pretype sbinder list -> pretype -> pretype
val applied_spine : preterm -> preterm list
val apply : preterm -> preterm list -> preterm
val apply_tele : preterm -> preterm sbinder list -> preterm
