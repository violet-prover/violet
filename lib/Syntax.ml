type preterm =
  | Universe
  | Var of string
and pretype = preterm
and binding = string * pretype
[@@deriving show]

type top =
  | Let of string * binding list * pretype  * preterm
[@@deriving show]
