open Bwd

type 't binder = { name : string; bound : 't; implicit : bool }
[@@deriving show]

module Surface = struct
  open Asai.Range

  type preterm =
    | Located of preterm located
        [@printer
          fun fmt { loc = _; value } -> fprintf fmt "%s" (show_preterm value)]
    | Universe [@printer fun fmt _ -> fprintf fmt "⋆"]
    | Hole [@printer fun fmt _ -> fprintf fmt "_"]
    | Var of string [@printer fun fmt name -> fprintf fmt "%s" name]
    | App of bool * preterm * preterm
        [@printer
          fun fmt (_, a, b) ->
            fprintf fmt "(%s %s)" (show_preterm a) (show_preterm b)]
    (* fun x => x *)
    | Lambda of preterm binder
        [@printer
          fun fmt bind ->
            if bind.implicit then
              fprintf fmt "fun {%s} => %s" bind.name (show_preterm bind.bound)
            else fprintf fmt "fun %s => %s" bind.name (show_preterm bind.bound)]
    | Pi of pretype binder * pretype
        [@printer
          fun fmt (bind, b) ->
            if bind.implicit then
              fprintf fmt "Π{%s : %s} -> %s" bind.name (show_pretype bind.bound)
                (show_pretype b)
            else
              fprintf fmt "Π(%s : %s) -> %s" bind.name (show_pretype bind.bound)
                (show_pretype b)]

  and pretype = preterm [@@deriving show]

  type as_arg = { term : preterm; implicit : bool }

  type top = Let of string * pretype binder list * pretype * preterm
  [@@deriving show]

  type t = { name : string; tops : top list } [@@deriving show]
end

module Core = struct
  type metavar = MetaVar of int [@printer fun fmt idx -> fprintf fmt "?%d" idx]
  [@@deriving show]

  type term =
    | Universe [@printer fun fmt _ -> fprintf fmt "⋆"]
    | Var of string [@printer fun fmt name -> fprintf fmt "%s" name]
    | App of term * term
    | Lambda of term binder
    | Pi of typ binder * typ
    | Meta of metavar
    (* TODO: 還沒有用到，還需要 bounds 紀錄當 meta 被插入時有哪些變數可以使用 *)
    | InsertedMeta of metavar

  and typ = term [@@deriving show]

  type value =
    | Flex of metavar * value bwd
        [@printer
          fun fmt (mhead, spine) ->
            if Bwd.is_empty spine then fprintf fmt "%s" (show_metavar mhead)
            else
              fprintf fmt "%s %s" (show_metavar mhead)
                (String.concat " " (List.map show_value @@ Bwd.to_list spine))]
    (* rigid 是一種 neutral value，是一個 bound variable applied 到 0..N 個引數後的產品 *)
    | Rigid of string * value bwd
        [@printer
          fun fmt (head, spine) ->
            if Bwd.is_empty spine then fprintf fmt "%s" head
            else
              fprintf fmt "%s %s" head
                (String.concat " " (List.map show_value @@ Bwd.to_list spine))]
    | VLambda of (value -> value)
        [@printer fun fmt _ -> fprintf fmt "<closure>"]
    | VPi of value_ty binder * (value -> value)
    | Universe [@printer fun fmt _ -> fprintf fmt "⋆"]
  [@@deriving show]

  and value_ty = value
end
