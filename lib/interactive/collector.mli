type t

val create : unit -> t
val on_event : t -> Violet_elab.Observer.event -> unit
val to_index : t -> Index.t
