open Bwd

(* Binders carry either a user-written name or `Anon` for binders generated
   internally (e.g. the non-dependent arrow `A -> B` desugars to a Pi whose
   binder is `Anon`, not `Named "_"`). Keeping the two distinct means a
   user-written `_` is just an ordinary `Named "_"` that can be referenced,
   while internal anonymous binders carry no string at all and can never
   be shadowed or captured by surface name lookup. *)
type binder_name =
  | Named of string
  | Anon
[@@deriving show]

module Name = struct
  type t = binder_name =
    | Named of string
    | Anon

  let to_string : t -> string = function
    | Named s -> s
    | Anon -> "_"
  ;;
end

type 't binder =
  { name : binder_name
  ; bound : 't
  ; implicit : bool
  }
[@@deriving show]

module Core = struct
  type metavar = MetaVar of int [@printer fun fmt idx -> fprintf fmt "?%d" idx]
  [@@deriving show]

  type term =
    | Universe of Level.level
    [@printer fun fmt l -> fprintf fmt "universe %s" (Level.pretty l)]
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
        then
          fprintf fmt "fun {%s} => %s" (Name.to_string bind.name) (show_term bind.bound)
        else fprintf fmt "fun %s => %s" (Name.to_string bind.name) (show_term bind.bound)]
    | TypedLambda of typ binder * term
    [@printer
      fun fmt (bind, body) ->
        if bind.implicit
        then
          fprintf
            fmt
            "fun {%s : %s} => %s"
            (Name.to_string bind.name)
            (show_typ bind.bound)
            (show_term body)
        else
          fprintf
            fmt
            "fun (%s : %s) => %s"
            (Name.to_string bind.name)
            (show_typ bind.bound)
            (show_term body)]
    | Pi of typ binder * typ
    [@printer
      fun fmt (bind, b) ->
        if bind.implicit
        then
          fprintf
            fmt
            "∀ {%s : %s} -> %s"
            (Name.to_string bind.name)
            (show_typ bind.bound)
            (show_typ b)
        else
          fprintf
            fmt
            "∀ (%s : %s) -> %s"
            (Name.to_string bind.name)
            (show_typ bind.bound)
            (show_typ b)]
    (* Meta 是使用者自己明確寫下來的那些 *)
    | Meta of metavar
    (* InsertedMeta 是 elaborator 自動塞進去的部分；payload 是插入時的 level 計數，
       evaluation 時透過 vapp_locals 套用到當下 env 的前 lvl 個 local *)
    | InsertedMeta of metavar * int
    [@printer fun fmt (m, n) -> fprintf fmt "%s[..%d]" (show_metavar m) n]
    | Lift of
        { from_lvl : Level.level
        ; to_lvl : Level.level
        ; ty : term
        }
    | LiftTerm of
        { from_lvl : Level.level
        ; to_lvl : Level.level
        ; ty : term
        ; tm : term
        }
    | UnliftTerm of
        { from_lvl : Level.level
        ; to_lvl : Level.level
        ; ty : term
        ; tm : term
        }
    | RecordType of
        { name : string
        ; params : term list
        ; fields : typ binder list
        }
    [@printer
      fun fmt aname aparams afields ->
        let p =
          match aparams with
          | [] -> ""
          | _ -> " " ^ String.concat " " (List.map show_term aparams)
        in
        let fs =
          String.concat
            " "
            (List.map
               (fun b -> "| " ^ Name.to_string b.name ^ " : " ^ show_typ b.bound)
               afields)
        in
        fprintf fmt "(record %s%s %s)" aname p fs]
    | RecordIntro of
        { name : string
        ; fields : (string * term) list
        }
    [@printer
      fun fmt aname afields ->
        let fs =
          String.concat ", " (List.map (fun (f, e) -> f ^ " = " ^ show_term e) afields)
        in
        fprintf fmt "%s{ %s }" aname fs]
    | RecordProj of
        { record : term
        ; field : string
        }
    [@printer fun fmt arecord afield -> fprintf fmt "%s.%s" (show_term arecord) afield]
    (* Disjointness primitive: given a term whose TYPE is `Id (c1 args1)
       (c2 args2)` with c1 ≠ c2 same-inductive constructors, IdAbsurd
       inhabits Empty. Elaborator verifies the type-shape; kernel treats
       it as a stuck neutral (never reduces because the underlying Id is
       uninhabited, so this term is never demanded at runtime). *)
    | IdAbsurd of term [@printer fun fmt t -> fprintf fmt "id-absurd %s" (show_term t)]

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
      (* Elim 是 inductive type 的 eliminator；head.reducer 帶 ι-rule。
         Evaluation.force_head 呼叫 reducer 嘗試 ι-reduce，否則 Elim 維持為
         neutral head with spine。 *)
    | Elim of elim_head * value bwd
    [@printer
      fun fmt ({ elim_name = head; _ }, spine) ->
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
                  | Elim (_, sp) | Var (_, sp) | Label (_, sp) | IndType (_, sp) ->
                    if Bwd.is_empty sp then show_value v else "(" ^ show_value v ^ ")"
                  | _ -> show_value v)
                @@ Bwd.to_list spine))]
    | VLambda of (value -> value) binder [@printer fun fmt _ -> fprintf fmt "<closure>"]
    | VPi of value_ty binder * (value -> value)
    [@printer
      fun fmt ({ name; bound; implicit }, closure) ->
        (* Printer 用 RigidLocal 0 當佔位；只是輸出用，跟實際 elaboration level 無關 *)
        let result = closure (RigidLocal (0, Bwd.Emp)) in
        let ns = Name.to_string name in
        if implicit
        then fprintf fmt "{%s : %s} -> %s" ns (show_value bound) (show_value result)
        else fprintf fmt "(%s : %s) -> %s" ns (show_value bound) (show_value result)]
    | Universe of Level.level
    [@printer fun fmt l -> fprintf fmt "universe %s" (Level.pretty l)]
    | VLift of
        { from_lvl : Level.level
        ; to_lvl : Level.level
        ; ty : value
        }
    | VLiftTerm of
        { from_lvl : Level.level
        ; to_lvl : Level.level
        ; ty : value
        ; tm : value
        }
    | VUnliftTerm of
        { from_lvl : Level.level
        ; to_lvl : Level.level
        ; ty : value
        ; tm : value
        }
    | VRecordType of
        { name : string
        ; params : value list
        ; fields : value_ty binder list
          (* Pre-instantiated with `rigid_local` placeholders for prior fields.
                 Consumers that only need to enumerate field names/types in
                 isolation use this directly. *)
        ; field_env : value bwd
          (* Env captured at construction time, before any field was placed.
                 Combine with `field_terms` to re-evaluate a field's type with
                 actual prior field values substituted in. *)
        ; field_terms : typ binder list
          (* Source-term form of fields, parallel to `fields`. Field i's
                 bound term, evaluated under `field_env <: v_0 <: ... <: v_{i-1}`,
                 yields the dependent type with prior fields substituted. *)
        }
    [@printer
      fun fmt aname aparams afields _aenv _aterms ->
        let p =
          match aparams with
          | [] -> ""
          | _ -> " " ^ String.concat " " (List.map show_value aparams)
        in
        let fs =
          String.concat
            " "
            (List.map
               (fun b -> "| " ^ Name.to_string b.name ^ " : " ^ show_value b.bound)
               afields)
        in
        fprintf fmt "(record %s%s %s)" aname p fs]
    | VRecordIntro of
        { name : string
        ; fields : (string * value) list
        }
    [@printer
      fun fmt aname afields ->
        let fs =
          String.concat ", " (List.map (fun (f, v) -> f ^ " = " ^ show_value v) afields)
        in
        fprintf fmt "%s{ %s }" aname fs]
    (* A (possibly stuck) field projection, with a spine of arguments applied to
       the projected field. The spine is non-empty only when the field has a
       function type and the projection is blocked on a neutral record, e.g.
       `r.f x` for a free variable `r` — there is no other place to hang the
       arguments since spines otherwise live on the leaf neutral heads. *)
    | VRecordProj of value * string * value bwd
    [@printer
      fun fmt (v, f, sp) ->
        if Bwd.is_empty sp
        then fprintf fmt "%s.%s" (show_value v) f
        else
          fprintf
            fmt
            "%s.%s %s"
            (show_value v)
            f
            (String.concat
               " "
               (List.map (fun u -> "(" ^ show_value u ^ ")") @@ Bwd.to_list sp))]
    (* Stuck-neutral value for [Core.IdAbsurd]: the underlying Id is
       uninhabited at type-check time, so this value never reduces. *)
    | VIdAbsurd of value [@printer fun fmt v -> fprintf fmt "id-absurd %s" (show_value v)]
  [@@deriving show]

  and elim_head =
    { elim_name : string
    ; reducer : (value bwd -> value option[@opaque])
    }

  and value_ty = value

  let rigid_local (lvl : int) : value = RigidLocal (lvl, Bwd.Emp)
  let lvl_to_ix ~(env_size : int) (lvl : int) : int = env_size - lvl - 1
end
