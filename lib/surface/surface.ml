open Yuujinchou

(* binder_name is shared with kernel *)
type binder_name = Violet_kernel.Syntax.binder_name =
  | Named of string
  | Anon
[@@deriving show]

(* Kernel binder, re-exported for the elaboration boundary. Surface code
   uses [sbinder] (located names); [forget_binder] crosses over. *)
type 't binder = 't Violet_kernel.Syntax.binder =
  { name : binder_name
  ; bound : 't
  ; implicit : bool
  }
[@@deriving show]

module Name = Violet_kernel.Syntax.Name

(* A value paired with the source range it was written at. Unlike asai's
   ['a located], the range is MANDATORY: synthesized values must inherit
   the range of whatever they derive from — a missing position is
   unrepresentable. *)
type 'a spanned =
  { loc : Asai.Range.t
  ; value : 'a
  }

(* Hand-written printer (used by [@@deriving show] below by naming
   convention): a spanned value prints as its payload; ranges stay out of
   debug output so expect-test goldens keep their current shape. *)
let pp_spanned pp_v fmt s = pp_v fmt s.value
let show_spanned show_v s = show_v s.value

type preterm =
  (preterm_record[@printer fun fmt t -> fprintf fmt "%s" (show_preterm_node t.node)])

and preterm_record =
  { loc : (Asai.Range.t[@opaque])
  ; node : preterm_node
  }

and preterm_node =
  | Universe [@printer fun fmt _ -> fprintf fmt "𝓤"]
  | Hole [@printer fun fmt _ -> fprintf fmt "_"]
  | Goal of string option
  [@printer
    fun fmt n ->
      match n with
      | Some s -> fprintf fmt "?%s" s
      | None -> fprintf fmt "?"]
  | Var of string list
  [@printer fun fmt path -> fprintf fmt "%s" (String.concat "/" path)]
  | App of bool * preterm * preterm
  [@printer
    fun fmt (implicit, a, b) ->
      if implicit
      then fprintf fmt "(%s {%s})" (show_preterm a) (show_preterm b)
      else fprintf fmt "(%s %s)" (show_preterm a) (show_preterm b)]
  (* fun x => M *)
  | Lambda of preterm sbinder
  [@printer
    fun fmt bind ->
      if bind.implicit
      then
        fprintf
          fmt
          "fun {%s} => %s"
          (Name.to_string bind.name.value)
          (show_preterm bind.bound)
      else
        fprintf
          fmt
          "fun %s => %s"
          (Name.to_string bind.name.value)
          (show_preterm bind.bound)]
  (* fun (x : T) => M *)
  | TypedLambda of pretype sbinder * preterm
  [@printer
    fun fmt (bind, body) ->
      if bind.implicit
      then
        fprintf
          fmt
          "fun {%s : %s} => %s"
          (Name.to_string bind.name.value)
          (show_pretype bind.bound)
          (show_preterm body)
      else
        fprintf
          fmt
          "fun (%s : %s) => %s"
          (Name.to_string bind.name.value)
          (show_pretype bind.bound)
          (show_preterm body)]
  | Pi of pretype sbinder * pretype
  [@printer
    fun fmt (bind, b) ->
      if bind.implicit
      then
        fprintf
          fmt
          "Π{%s : %s} -> %s"
          (Name.to_string bind.name.value)
          (show_pretype bind.bound)
          (show_pretype b)
      else
        fprintf
          fmt
          "Π(%s : %s) -> %s"
          (Name.to_string bind.name.value)
          (show_pretype bind.bound)
          (show_pretype b)]
  | Max of preterm * preterm
  [@printer fun fmt (a, b) -> fprintf fmt "(%s ⊔ %s)" (show_preterm a) (show_preterm b)]
  (* Flat sequence of soup items emitted by the parser before operator
     resolution. The resolver walks the whole module and rewrites every
     Op_soup into App/Var/etc.; nothing downstream should ever see it. *)
  | Op_soup of soup_item list
  [@printer
    fun fmt items ->
      fprintf fmt "<soup:[%s]>" (String.concat "; " (List.map show_soup_item items))]
  | RecordLit of (string spanned * preterm) list
  [@printer
    fun fmt aentries ->
      fprintf
        fmt
        "{ %s }"
        (String.concat
           ", "
           (List.map (fun (f, e) -> f.value ^ " = " ^ show_preterm e) aentries))]
  | RecordUpdate of preterm * (string spanned * preterm) list
  [@printer
    fun fmt (base, entries) ->
      fprintf
        fmt
        "{ %s | %s }"
        (show_preterm base)
        (String.concat
           ", "
           (List.map (fun (f, e) -> f.value ^ " = " ^ show_preterm e) entries))]
  | Proj of preterm * string spanned
  [@printer fun fmt (e, f) -> fprintf fmt "%s.%s" (show_preterm e) f.value]
  (* Builtin disjointness primitive: `\absurd-id <p>` where `p` has type
     `Id (c1 args1) (c2 args2)` for distinct same-inductive constructors
     `c1` and `c2`. Elaborates to `Core.IdAbsurd` with type `Empty`.
     Generated only by [Inductive.build_elim_body_unify] to discharge
     unreachable cases; no surface syntax. *)
  | IdAbsurd of preterm
  [@printer fun fmt p -> fprintf fmt "(\\absurd-id %s)" (show_preterm p)]
  | Absurd of preterm [@printer fun fmt p -> fprintf fmt "(absurd %s)" (show_preterm p)]
  | Inline_elim of inline_elim_data
  [@printer fun fmt d -> fprintf fmt "(<= elim %s)" d.target]

(* Surface binder: like the kernel binder but the bound name remembers
   where it was written. *)
and 't sbinder =
  { name : binder_name spanned
  ; bound : 't
  ; implicit : bool
  }

and inline_elim_data =
  { target : string
  ; siblings : (clause * pattern list) list
  ; outer_subst : (int * Violet_kernel.Syntax.Core.value) list
        [@printer fun fmt _ -> fprintf fmt "[..subst..]"]
  ; target_override : preterm option
  }

and soup_item =
  | SI_Atom of preterm [@printer fun fmt p -> fprintf fmt "A(%s)" (show_preterm p)]
  | SI_Name of string spanned [@printer fun fmt s -> fprintf fmt "N(%s)" s.value]
  | SI_Imp_arg of preterm [@printer fun fmt p -> fprintf fmt "I{%s}" (show_preterm p)]

and pretype = preterm

and pattern =
  (pattern_record[@printer fun fmt p -> fprintf fmt "%s" (show_pattern_node p.pnode)])

and pattern_record =
  { ploc : (Asai.Range.t[@opaque])
  ; pnode : pattern_node
  }

and pattern_node =
  | PVar of string
  | PWildcard
  | PCon of string spanned * pattern list
  | PImpVar of string
  | PRecord of (string spanned * pattern) list

and clause =
  { head : string spanned
  ; patterns : pattern list
  ; body : preterm
  }
[@@deriving show]

type as_arg =
  { term : preterm
  ; implicit : bool
  }

type stack_move =
  | Intro
  | Split
[@@deriving show]

(* A name path naming another operator in cross-reference position: the
   referenced operator's literal parts, in template order. E.g., template
   `"\x + \y"` is referenced as `["+"]`; template `"if \x then \y else \z"`
   as `["if"; "then"; "else"]`. *)
type op_name_path = string list [@@deriving show]

type op_assoc =
  | OA_Left
  | OA_Right
  | OA_None
[@@deriving show]

type op_option =
  | OO_Weaker_than of op_name_path list
  | OO_Stronger_than of op_name_path list
  | OO_Same_as of op_name_path list
  | OO_Associativity of op_assoc
[@@deriving show]

type top =
  | Let of
      { name : string spanned
      ; bindings : pretype sbinder list
      ; result_ty : pretype
      ; body : preterm
      }
  (* `\data <name> <params> : <deps> -> <ind_ty> | <ctors>`.
     Constructor-name locations live in each ctor sbinder's [name.loc]. *)
  | Data of
      { name : string spanned
      ; params : pretype sbinder list
      ; deps : pretype sbinder list
      ; ind_ty : pretype
      ; ctors : pretype sbinder list
      }
  (* `\universe U V W` declares per-module level variables. *)
  | Universe_decl of string spanned list
  (*
     let <name> <params> : <signature> where
       <moves>
       | <clause>
       | ...
  *)
  | Stack_def of
      { name : string spanned
      ; params : pretype sbinder list
      ; signature : pretype
      ; moves : stack_move list
      ; clauses : clause list
      }
  (*
     let <name> <params> : <signature> where
       open <Inductive>     # optional, repeatable
       ...
       <name> <intros> <= elim <target>
       | <clause>
       | ...
     `params` are the typed binders from the signature; `intros` are the
     untyped names on the guard line, one per Pi-layer of the signature
     past `params`. `target` must equal one of `intros`. `opens` lists
     inductive names whose ctors are usable unqualified in clause bodies.
  *)
  | Elim_def of
      { name : string spanned
      ; params : pretype sbinder list
      ; signature : pretype
      ; opens : string list
      ; intros : (string spanned * bool) list
      ; target : string spanned
      ; clauses : clause list
      }
  (*
     \operator "\x + \y" => add
       \associativity: \left
       \stronger_than: *
     The template is a raw string with whitespace-separated parts; the body
     is an arbitrary preterm whose free vars include the hole names from
     the template; options control precedence / associativity.
  *)
  | Operator_decl of
      { template : string
      ; body : preterm
      ; options : op_option list
      }
  | Record of
      { name : string spanned
      ; params : pretype sbinder list
      ; ind_ty : pretype
      ; fields : pretype sbinder list
      }
[@@deriving show]

type t =
  { name : string
  ; imports : Trie.path list (* import libraries *)
  ; exports : string spanned list
  ; tops : top spanned list
  }

(* Re-exported from [Violet_common.Range] so Surface callers keep their
   historical names. *)
let join_loc = Violet_common.Range.join
let dummy_loc = Violet_common.Range.dummy

module Mk = struct
  let at (loc : Asai.Range.t) (node : preterm_node) : preterm = { loc; node }
  let re_loc (loc : Asai.Range.t) (t : preterm) : preterm = { t with loc }
  let sn (loc : Asai.Range.t) (value : 'a) : 'a spanned = { loc; value }

  (* Dummy-located constructors, for synthesized terms with no better
     provenance (whitebox tests, REPL, builtin elaboration). *)
  let d (node : preterm_node) : preterm = { loc = dummy_loc; node }
  let dn (value : 'a) : 'a spanned = { loc = dummy_loc; value }
end

(* Cross to the kernel binder, dropping the name's location. *)
let forget_binder (b : 't sbinder) : 't Violet_kernel.Syntax.binder =
  { name = b.name.value; bound = b.bound; implicit = b.implicit }
;;

let rec lambda (names : string spanned list) (body : preterm) : preterm =
  match names with
  | [] -> body
  | p :: ps ->
    let inner = lambda ps body in
    { loc = join_loc p.loc inner.loc
    ; node =
        Lambda
          { name = { loc = p.loc; value = Named p.value }
          ; bound = inner
          ; implicit = false
          }
    }
;;

let rec typed_lambda (binds : pretype sbinder list) (body : preterm) : preterm =
  match binds with
  | [] -> body
  | b :: bs ->
    let inner = typed_lambda bs body in
    { loc = join_loc b.name.loc inner.loc; node = TypedLambda (b, inner) }
;;

let rec telescope (t : pretype) : pretype sbinder list =
  match t.node with
  | Pi (bind, body) -> bind :: telescope body
  | _ -> []
;;

let rec codomain (t : pretype) : pretype =
  match t.node with
  | Pi (_, body) -> codomain body
  | _ -> t
;;

let rec pi (tele : pretype sbinder list) (result : pretype) : pretype =
  match tele with
  | [] -> result
  | b :: bs ->
    let body = pi bs result in
    { loc = join_loc b.name.loc body.loc; node = Pi (b, body) }
;;

let rec applied_spine (t : preterm) : preterm list =
  match t.node with
  | App (_, f, arg) -> applied_spine f @ [ arg ]
  | _ -> []
;;

let rec apply (f : preterm) (args : preterm list) : preterm =
  match f, args with
  | f, [] -> f
  | f, x :: xs -> apply { loc = join_loc f.loc x.loc; node = App (false, f, x) } xs
;;

let rec apply_tele (f : preterm) (tele : preterm sbinder list) : preterm =
  match f, tele with
  | f, [] -> f
  | f, { name; implicit; _ } :: xs ->
    let arg = { loc = name.loc; node = Var [ Name.to_string name.value ] } in
    apply_tele { loc = join_loc f.loc name.loc; node = App (implicit, f, arg) } xs
;;

let%expect_test "applied spine" =
  let v s = Mk.at dummy_loc (Var [ s ]) in
  let result = applied_spine (apply (v "a") [ v "b"; v "c" ]) in
  print_string @@ [%show: preterm list] result;
  [%expect {| [b; c] |}]
;;
