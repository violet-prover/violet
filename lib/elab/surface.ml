open Asai.Range
open Yuujinchou

(* binder is shared with kernel *)
type 't binder = 't Violet_kernel.Syntax.binder =
  { name : string
  ; bound : 't
  ; implicit : bool
  }
[@@deriving show]

type preterm =
  | Located of preterm located
  [@printer fun fmt { loc = _; value } -> fprintf fmt "%s" (show_preterm value)]
  | Universe [@printer fun fmt _ -> fprintf fmt "𝓤"]
  | Hole [@printer fun fmt _ -> fprintf fmt "_"]
  | Goal of string option
  [@printer
    fun fmt n ->
      match n with
      | Some s -> fprintf fmt "?%s" s
      | None -> fprintf fmt "?"]
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
  | Max of preterm * preterm
  [@printer fun fmt (a, b) -> fprintf fmt "(%s ⊔ %s)" (show_preterm a) (show_preterm b)]

and pretype = preterm [@@deriving show]

type as_arg =
  { term : preterm
  ; implicit : bool
  }

type stack_move =
  | Intro
  | Split
[@@deriving show]

type pattern =
  | PVar of string
  | PCon of string * string list
  | PImpVar of string
[@@deriving show]

type clause =
  { head : string
  ; patterns : pattern list
  ; body : preterm
  }
[@@deriving show]

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
  (* `universe U V W` declares per-module level variables. *)
  | Universe_decl of string list
  (*
     let <name> <params> : <signature> where
       <moves>
       | <clause>
       | ...
  *)
  | Stack_def of
      { name : string
      ; params : pretype binder list
      ; signature : pretype
      ; moves : stack_move list
      ; clauses : clause list
      }
  (*
     let <name> <params> : <signature> where
       <name> <intros> <= elim <target>
       | <clause>
       | ...
     `params` are the typed binders from the signature; `intros` are the
     untyped names on the guard line, one per Pi-layer of the signature
     past `params`. `target` must equal one of `intros`.
  *)
  | Elim_def of
      { name : string
      ; params : pretype binder list
      ; signature : pretype
      ; intros : (string * bool) list
      ; target : string
      ; clauses : clause list
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

let%expect_test "applied spine" =
  let result = applied_spine (apply (Var "a") [ Var "b"; Var "c" ]) in
  print_string @@ [%show: preterm list] result;
  [%expect {| [b; c] |}]
;;
