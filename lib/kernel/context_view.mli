type t

val empty : t
val make : names:string Bwd.bwd -> lvl:int -> t
val extend : t -> string -> t
val lvl : t -> int
val nth_name_from_lvl : t -> int -> string option
