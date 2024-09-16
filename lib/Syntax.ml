open Bwd

module Surface = struct
  type preterm = Universe | Var of string
  and pretype = preterm
  and binding = string * pretype
  [@@deriving show]

  type top = Let of string * binding list * pretype * preterm
  [@@deriving show]

  type t = { name : string; tops : top list }
  [@@deriving show]
end

module Core = struct
  type metavar = MetaVar of int [@@deriving show]

  type term =
    | Universe [@printer fun fmt _ -> fprintf fmt "⋆"]
    | Var of string [@printer fun fmt name -> fprintf fmt "%s" name]
    | Meta of metavar
    (* TODO: 還沒有用到，還需要 bounds 紀錄當 meta 被插入時有哪些變數可以使用 *)
    | InsertedMeta of metavar
  and typ = term
  [@@deriving show]

  type value =
    | Flex of metavar * value bwd
        [@printer
          fun fmt (mhead, spine) ->
            if Bwd.is_empty spine then
              fprintf fmt "%s" (show_metavar mhead)
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
    | Lambda of (value -> value) [@printer fun fmt _ -> fprintf fmt "<closure>"]
    | Pi of string * value_ty
    | Universe
  [@@deriving show]
  and value_ty = value
end
