module type S = sig
  val name : string
  val wrap_block : string -> string
  val passthrough : string -> string
end

(* tr-notes: Wrapping the highlighted HTML in [@pre|{...}|].
   The highlighter guarantees its output never contains the [}|] that
   would close the body early (it escapes [|]). *)
module Tr_notes : S = struct
  let name = "tr-notes"
  let wrap_block html = "@pre|{" ^ html ^ "}|"
  let passthrough s = s
end
