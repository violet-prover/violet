open Syntax

module type META_VIEW = sig
  val lookup : Core.metavar -> Core.value option
  val eval : Core.metavar -> Core.value

  (* True for metas that stand in for a user-placed `?` goal.  Such metas are
     intentionally left unsolved; well-formedness checks treat them as known
     so goal-bearing declarations can still enter the module. *)
  val is_goal : Core.metavar -> bool
end

module type ENV_VIEW = sig
  val lookup : string -> Core.value
  val unfold : string -> Core.value option
end
