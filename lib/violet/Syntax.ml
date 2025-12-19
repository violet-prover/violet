open Bwd
open Yuujinchou

type 't binder =
  { name : string
  ; bound : 't
  ; implicit : bool
  }
[@@deriving show]

module Surface = struct
  open Asai.Range

  type preterm =
    | Located of preterm located
    [@printer fun fmt { loc = _; value } -> fprintf fmt "%s" (show_preterm value)]
    | Universe [@printer fun fmt _ -> fprintf fmt "𝓤"]
    | Hole [@printer fun fmt _ -> fprintf fmt "_"]
    | Var of string [@printer fun fmt name -> fprintf fmt "%s" name]
    | App of bool * preterm * preterm
    [@printer
      fun fmt (implicit, a, b) ->
        if implicit
        then fprintf fmt "(%s {%s})" (show_preterm a) (show_preterm b)
        else fprintf fmt "(%s %s)" (show_preterm a) (show_preterm b)]
    (* fun x => M *)
    (* so we record (x , M) *)
    | Lambda of preterm binder
    [@printer
      fun fmt bind ->
        if bind.implicit
        then fprintf fmt "fun {%s} => %s" bind.name (show_preterm bind.bound)
        else fprintf fmt "fun %s => %s" bind.name (show_preterm bind.bound)]
    (* fun (x : T) => M *)
    (* so we record (x , T , M) *)
    | TypedLambda of pretype binder * preterm
    [@printer
      fun fmt (bind, body) ->
        if bind.implicit
        then
          fprintf
            fmt
            "fun {%s : %s} => %s"
            bind.name
            (show_pretype bind.bound)
            (show_preterm body)
        else
          fprintf
            fmt
            "fun (%s : %s) => %s"
            bind.name
            (show_pretype bind.bound)
            (show_preterm body)]
    | Pi of pretype binder * pretype
    [@printer
      fun fmt (bind, b) ->
        if bind.implicit
        then
          fprintf
            fmt
            "Π{%s : %s} -> %s"
            bind.name
            (show_pretype bind.bound)
            (show_pretype b)
        else
          fprintf
            fmt
            "Π(%s : %s) -> %s"
            bind.name
            (show_pretype bind.bound)
            (show_pretype b)]

  and pretype = preterm [@@deriving show]

  type as_arg =
    { term : preterm
    ; implicit : bool
    }

  type top =
    | Let of string * pretype binder list * pretype * preterm
    (*
       data <name> : <ind_ty> where
         <clauses>
    *)
    | Data of
        { name : string
        ; params : pretype binder list
        ; ind_ty : pretype
        ; clauses : pretype binder list
        }
  [@@deriving show]

  type t =
    { name : string
    ; imports : Trie.path list (* import libraries *)
    ; tops : top Asai.Range.located list
    }

  let rec lambda (names : string list) (body : preterm) : preterm =
    match names with
    | [] -> body
    | p :: ps -> Lambda { name = p; bound = lambda ps body; implicit = false }
  ;;

  let rec typed_lambda (binds : pretype binder list) (body : preterm) : preterm =
    match binds with
    | [] -> body
    | b :: bs -> TypedLambda (b, typed_lambda bs body)
  ;;

  let rec telescope : pretype -> pretype binder list = function
    | Located { value = p; _ } -> telescope p
    | Pi (bind, body) -> bind :: telescope body
    | _ -> []
  ;;

  let rec pi (tele : pretype binder list) (result : pretype) : pretype =
    match tele with
    | [] -> result
    | b :: bs -> Pi (b, pi bs result)
  ;;

  let rec apply (f : preterm) (args : preterm list) : preterm =
    match f, args with
    | f, [] -> f
    | f, x :: xs -> apply (App (false, f, x)) xs
  ;;

  let rec apply_tele (f : preterm) (tele : preterm binder list) : preterm =
    match f, tele with
    | f, [] -> f
    | f, { name; implicit; _ } :: xs -> apply_tele (App (implicit, f, Var name)) xs
  ;;
end

module Core = struct
  type metavar = MetaVar of int [@printer fun fmt idx -> fprintf fmt "?%d" idx]
  [@@deriving show]

  type term =
    | Universe [@printer fun fmt _ -> fprintf fmt "𝓤"]
    | Var of string [@printer fun fmt name -> fprintf fmt "%s" name]
    | App of term * term
    [@printer fun fmt (a, b) -> fprintf fmt "%s %s" (show_term a) (show_term b)]
    | Lambda of term binder
    [@printer
      fun fmt bind ->
        if bind.implicit
        then fprintf fmt "fun {%s} => %s" bind.name (show_term bind.bound)
        else fprintf fmt "fun %s => %s" bind.name (show_term bind.bound)]
    | TypedLambda of typ binder * term
    [@printer
      fun fmt (bind, body) ->
        if bind.implicit
        then
          fprintf
            fmt
            "fun {%s : %s} => %s"
            bind.name
            (show_typ bind.bound)
            (show_term body)
        else
          fprintf
            fmt
            "fun (%s : %s) => %s"
            bind.name
            (show_typ bind.bound)
            (show_term body)]
    | Pi of typ binder * typ
    [@printer
      fun fmt (bind, b) ->
        if bind.implicit
        then fprintf fmt "∀ {%s : %s} -> %s" bind.name (show_typ bind.bound) (show_typ b)
        else fprintf fmt "∀ (%s : %s) -> %s" bind.name (show_typ bind.bound) (show_typ b)]
    (* Meta 是使用者自己明確寫下來的那些 *)
    | Meta of metavar
    (* InsertedMeta 是 elaborator 自動塞進去的部分，所以需要紀錄 context 中的變數 *)
    | InsertedMeta of metavar * string bwd
    [@printer
      fun fmt (m, vars) ->
        fprintf fmt "%s %s" (show_metavar m) (String.concat " " (Bwd.to_list vars))]

  and typ = term [@@deriving show]

  type value =
    | Flex of metavar * value bwd
    [@printer
      fun fmt (mhead, locals) ->
        if Bwd.is_empty locals
        then fprintf fmt "%s" (show_metavar mhead)
        else
          fprintf
            fmt
            "%s(%s)"
            (show_metavar mhead)
            (String.concat ", " (List.map show_value @@ Bwd.to_list locals))]
    (* rigid 是一種 neutral value，是一個 bound variable applied 到 0..N 個引數後的產品 *)
    | Rigid of string * value bwd
    [@printer
      fun fmt (head, spine) ->
        if Bwd.is_empty spine
        then fprintf fmt "%s" head
        else
          fprintf
            fmt
            "%s %s"
            head
            (String.concat
               " "
               (List.map (fun v ->
                  match v with
                  | Rigid (_, sp) ->
                    if Bwd.is_empty sp then show_value v else "(" ^ show_value v ^ ")"
                  | _ -> show_value v)
                @@ Bwd.to_list spine))]
      (* indtype 是 inductive type 在 environment 裡面的表示方式，跟 rigid 要分開 *)
    | IndType of string * value bwd
    [@printer
      fun fmt (head, spine) ->
        if Bwd.is_empty spine
        then fprintf fmt "%s" head
        else
          fprintf
            fmt
            "%s %s"
            head
            (String.concat
               " "
               (List.map (fun v ->
                  match v with
                  | Label (_, sp) ->
                    if Bwd.is_empty sp then show_value v else "(" ^ show_value v ^ ")"
                  | _ -> show_value v)
                @@ Bwd.to_list spine))]
      (* label 是 constructor 的表示方式，跟 rigid 要分開 *)
    | Label of string * value bwd
    [@printer
      fun fmt (head, spine) ->
        if Bwd.is_empty spine
        then fprintf fmt "%s" head
        else
          fprintf
            fmt
            "%s %s"
            head
            (String.concat
               " "
               (List.map (fun v ->
                  match v with
                  | Label (_, sp) ->
                    if Bwd.is_empty sp then show_value v else "(" ^ show_value v ^ ")"
                  | _ -> show_value v)
                @@ Bwd.to_list spine))]
    | VLambda of (value -> value) binder [@printer fun fmt _ -> fprintf fmt "<closure>"]
    | VPi of value_ty binder * (value -> value)
    [@printer
      fun fmt ({ name; bound; implicit }, closure) ->
        let result = closure (Rigid (name, Bwd.Emp)) in
        if implicit
        then fprintf fmt "{%s : %s} -> %s" name (show_value bound) (show_value result)
        else fprintf fmt "(%s : %s) -> %s" name (show_value bound) (show_value result)]
    | Universe [@printer fun fmt _ -> fprintf fmt "𝓤"]
  [@@deriving show]

  and value_ty = value
end
