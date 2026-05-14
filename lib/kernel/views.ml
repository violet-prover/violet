open Syntax

module type META_VIEW = sig
  val lookup : Core.metavar -> Core.value option
  val eval : Core.metavar -> Core.value
end

module type ENV_VIEW = sig
  val lookup : string -> Core.value
  val unfold : string -> Core.value option
end
