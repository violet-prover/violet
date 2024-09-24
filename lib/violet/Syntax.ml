open Bwd

type 't binder = { name : string; bound : 't; implicit : bool }
[@@deriving show]

module Surface = struct
  open Asai.Range

  type preterm =
    | Located of preterm located
        [@printer
          fun fmt { loc = _; value } -> fprintf fmt "%s" (show_preterm value)]
    | Universe [@printer fun fmt _ -> fprintf fmt "𝓤"]
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

  type top =
    | Let of string * pretype binder list * pretype * preterm
    | Data of { name : string; ind_ty : pretype; clauses : pretype binder list }
  [@@deriving show]

  type t = { name : string; tops : top Asai.Range.located list }
end

module Core = struct
  type metavar =
    | MetaVar of int [@printer fun fmt idx -> fprintf fmt "?%d" idx]
  [@@deriving show]

  type term =
    | Universe [@printer fun fmt _ -> fprintf fmt "𝓤"]
    | Var of string [@printer fun fmt name -> fprintf fmt "%s" name]
    | App of term * term
        [@printer
          fun fmt (a, b) -> fprintf fmt "%s %s" (show_term a) (show_term b)]
    | Lambda of term binder
        [@printer
          fun fmt bind ->
            if bind.implicit then
              fprintf fmt "fun {%s} => %s" bind.name (show_term bind.bound)
            else fprintf fmt "fun %s => %s" bind.name (show_term bind.bound)]
    | Pi of typ binder * typ
    (* Meta 是使用者自己明確寫下來的那些 *)
    | Meta of metavar
    (* InsertedMeta 是 elaborator 自動塞進去的部分，所以需要紀錄 context 中的變數 *)
    | InsertedMeta of metavar * string bwd
        [@printer
          fun fmt (m, vars) ->
            fprintf fmt "%s %s" (show_metavar m)
              (String.concat " " (Bwd.to_list vars))]

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
    | VLambda of (value -> value) binder
        [@printer fun fmt _ -> fprintf fmt "<closure>"]
    | VPi of value_ty binder * (value -> value)
    | Universe [@printer fun fmt _ -> fprintf fmt "𝓤"]
  [@@deriving show]

  and value_ty = value
end
