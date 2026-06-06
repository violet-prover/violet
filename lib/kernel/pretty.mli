val pp_local_name : Context_view.t -> int -> string
val pp_universe : Level.level -> string
val pp_level : Level.level -> string
val pp_metavar : Syntax.Core.metavar -> string

(* A notation hook lets the caller render a named head applied to explicit
   arguments as user-defined operator syntax. [pp_arg] is the recursive
   argument printer — context- and notation-aware, parenthesizing non-atomic
   arguments. Return [None] to fall back to the default rendering. *)
type 'a notation_hook =
  pp_arg:('a -> string) -> head:string -> explicit_args:'a list -> string option

val pp_value
  :  ?notation:Syntax.Core.value notation_hook
  -> Context_view.t
  -> Syntax.Core.value
  -> string

val pp_term
  :  ?notation:Syntax.Core.term notation_hook
  -> Context_view.t
  -> Syntax.Core.term
  -> string
