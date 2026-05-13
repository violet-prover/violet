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
       data <name> <params> : <deps> <ind_ty> where
         <ctors>
    *)
    | Data of
        { name : string (* parameters is a list of bindings that will be opaque *)
        ; params : pretype binder list
          (* dependencies is a list of bindings that can be concrete *)
        ; deps : pretype binder list (* ind_ty should always be U *)
        ; ind_ty : pretype
        ; ctors : pretype binder list
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

  let rec codomain : pretype -> pretype = function
    | Located { value = p; _ } -> codomain p
    | Pi (_, body) -> codomain body
    | t -> t
  ;;

  let rec pi (tele : pretype binder list) (result : pretype) : pretype =
    match tele with
    | [] -> result
    | b :: bs -> Pi (b, pi bs result)
  ;;

  let rec applied_spine (t : preterm) : preterm list =
    match t with
    | App (_, f, arg) -> applied_spine f @ [ arg ]
    | _ -> []
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
    (* local variable: de Bruijn INDEX (0 = innermost binder) *)
    | LocalVar of int [@printer fun fmt i -> fprintf fmt "$%d" i]
    (* global name: top-level let / data / constructor *)
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
    (* InsertedMeta 是 elaborator 自動塞進去的部分；payload 是插入時的 level 計數，
       evaluation 時透過 vapp_locals 套用到當下 env 的前 lvl 個 local *)
    | InsertedMeta of metavar * int
    [@printer fun fmt (m, n) -> fprintf fmt "%s[..%d]" (show_metavar m) n]

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
    (* local-bound free variable: de Bruijn LEVEL (counted from the outside in)。
       Lambda/Pi 開新 binder 時直接拿當下的 lvl 來生這個 head。 *)
    | RigidLocal of int * value bwd
    [@printer
      fun fmt (lvl, spine) ->
        if Bwd.is_empty spine
        then fprintf fmt "$%d" lvl
        else
          fprintf
            fmt
            "$%d %s"
            lvl
            (String.concat
               " "
               (List.map (fun v ->
                  match v with
                  | RigidLocal (_, sp) ->
                    if Bwd.is_empty sp then show_value v else "(" ^ show_value v ^ ")"
                  | _ -> show_value v)
                @@ Bwd.to_list spine))]
    (* opaque global head：top-level let 還沒展開時的 representation。
       Unfold 由 Unification 視需要呼叫 Env.unfold_def 觸發。 *)
    | Var of string * value bwd
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
                  | Var (_, sp) ->
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
        (* Printer 用 RigidLocal 0 當佔位；只是輸出用，跟實際 elaboration level 無關 *)
        let result = closure (RigidLocal (0, Bwd.Emp)) in
        if implicit
        then fprintf fmt "{%s : %s} -> %s" name (show_value bound) (show_value result)
        else fprintf fmt "(%s : %s) -> %s" name (show_value bound) (show_value result)]
    | Universe [@printer fun fmt _ -> fprintf fmt "𝓤"]
  [@@deriving show]

  and value_ty = value

  let rigid_local (lvl : int) : value = RigidLocal (lvl, Bwd.Emp)
  let lvl_to_ix ~(env_size : int) (lvl : int) : int = env_size - lvl - 1
end

let%expect_test "applied spine" =
  let result =
    Surface.applied_spine
      (Surface.apply (Surface.Var "a") [ Surface.Var "b"; Surface.Var "c" ])
  in
  print_string @@ [%show: Surface.preterm list] result;
  [%expect {| [b; c] |}]
;;
