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
  type metavar = MetaVar of int

  type term =
    | Universe of Level.level
    (* local variable: de Bruijn INDEX (0 = innermost binder) *)
    | LocalVar of int
    (* global name: top-level let / data / constructor *)
    | Var of string
    | App of term * term * (* implicit 的指標，這個完全不影響 kernel 計算 *) bool
    | Lambda of term binder
    | TypedLambda of typ binder * term
    | Pi of typ binder * typ
    (* Meta 是使用者自己明確寫下來的那些 *)
    | Meta of metavar
    (* InsertedMeta 是 elaborator 自動塞進去的部分；payload 是插入時的 level 計數，
       evaluation 時透過 vapp_locals 套用到當下 env 的前 lvl 個 local *)
    | InsertedMeta of metavar * int
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
    | RecordIntro of
        { name : string
        ; fields : (string * term) list
        }
    | RecordProj of
        { record : term
        ; field : string
        }
    (* Disjointness primitive: given a term whose TYPE is `Id (c1 args1)
       (c2 args2)` with c1 ≠ c2 same-inductive constructors, IdAbsurd
       inhabits Empty. Elaborator verifies the type-shape; kernel treats
       it as a stuck neutral (never reduces because the underlying Id is
       uninhabited, so this term is never demanded at runtime). *)
    | IdAbsurd of term
    (* The empty type: a builtin with no constructors. Always available;
       not defined in any .vt source. *)
    | Empty
    (* Ex-falso. [scrut] has type [Empty]; this term inhabits any type. The
       elaborator places it only in dead `\elim` branches. Kernel treats it
       as a stuck neutral (Empty is uninhabited, so it never reduces). *)
    | Absurd of term

  and typ = term

  type value =
    | Flex of metavar * spine
    (* local-bound free variable: de Bruijn LEVEL (counted from the outside in)。
       Lambda/Pi 開新 binder 時直接拿當下的 lvl 來生這個 head。 *)
    | RigidLocal of int * spine
    (* opaque global head：top-level let 還沒展開時的 representation。
       Unfold 由 Unification 視需要呼叫 Env.unfold_def 觸發。 *)
    | Var of string * spine
      (* indtype 是 inductive type 在 environment 裡面的表示方式，跟 rigid 要分開 *)
    | IndType of string * spine (* label 是 constructor 的表示方式，跟 rigid 要分開 *)
    | Label of string * spine
      (* Elim 是 inductive type 的 eliminator；head.reducer 帶 ι-rule。
         Evaluation.force_head 呼叫 reducer 嘗試 ι-reduce，否則 Elim 維持為
         neutral head with spine。 *)
    | Elim of elim_head * spine
    | VLambda of (value -> value) binder
    | VPi of value_ty binder * (value -> value)
    | Universe of Level.level
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
    | VRecordIntro of
        { name : string
        ; fields : (string * value) list
        }
    (* A (possibly stuck) field projection, with a spine of arguments applied to
       the projected field. The spine is non-empty only when the field has a
       function type and the projection is blocked on a neutral record, e.g.
       `r.f x` for a free variable `r` — there is no other place to hang the
       arguments since spines otherwise live on the leaf neutral heads. *)
    | VRecordProj of value * string * spine
    (* Stuck-neutral value for [Core.IdAbsurd]: the underlying Id is
       uninhabited at type-check time, so this value never reduces. *)
    | VIdAbsurd of value
    | VEmpty
    (* Stuck-neutral ex-falso with its spine: when the inhabited type is a
       function, the value may be applied, so arguments accumulate here. *)
    | VAbsurd of value * spine

  and elim_head =
    { elim_name : string
    ; reducer : spine -> value option
    }

  and value_ty = value

  (* One applied argument on a neutral spine: the argument value together with
     whether it was supplied implicitly.  [implicit] is display-only metadata
     (see [App]); spine equality and reduction look only at [tm]. *)
  and arg =
    { tm : value
    ; implicit : bool
    }

  and spine = arg bwd

  let rigid_local (lvl : int) : value = RigidLocal (lvl, Bwd.Emp)
  let lvl_to_ix ~(env_size : int) (lvl : int) : int = env_size - lvl - 1

  (* Build an explicit / implicit spine argument. *)
  let explicit_arg (v : value) : arg = { tm = v; implicit = false }
  let implicit_arg (v : value) : arg = { tm = v; implicit = true }

  (* Drop the implicit flags, recovering the bare argument values. *)
  let spine_values (sp : spine) : value Bwd.t = Bwd.map (fun a -> a.tm) sp
end
