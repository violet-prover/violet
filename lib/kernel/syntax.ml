open Bwd

type 't binder =
  { name : string
  ; bound : 't
  ; implicit : bool
  }
[@@deriving show]

module Core = struct
  type metavar = MetaVar of int [@printer fun fmt idx -> fprintf fmt "?%d" idx]
  [@@deriving show]

  type term =
    | Universe of Level.level
    [@printer
      fun fmt l ->
        if Level.equal l Level.LZero
        then fprintf fmt "𝓤"
        else fprintf fmt "𝓤(%s)" (Level.show_level l)]
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
      (* Elim 是一個 inductive type 的 eliminator。head.reducer 帶著 ι-rule。
         Evaluation.force_head 在 spine 足夠時呼叫 reducer 看能不能 ι-reduce；
         否則 Elim 維持像個帶 spine 的 neutral head。 *)
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
        if implicit
        then fprintf fmt "{%s : %s} -> %s" name (show_value bound) (show_value result)
        else fprintf fmt "(%s : %s) -> %s" name (show_value bound) (show_value result)]
    | Universe of Level.level
    [@printer
      fun fmt l ->
        if Level.equal l Level.LZero
        then fprintf fmt "𝓤"
        else fprintf fmt "𝓤(%s)" (Level.show_level l)]
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
  [@@deriving show]

  and elim_head =
    { elim_name : string
    ; reducer : (value bwd -> value option[@opaque])
    }

  and value_ty = value

  let rigid_local (lvl : int) : value = RigidLocal (lvl, Bwd.Emp)
  let lvl_to_ix ~(env_size : int) (lvl : int) : int = env_size - lvl - 1
end
