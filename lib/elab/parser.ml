(* Typed-algebraic parser combinators (Krishnaswami-style).
   Strictly LL(1) at the combinator level, with two small
   hand-coded disambiguators that peek the token buffer:

     1. `(` ... : in atom position, peek for `IDENT+ :` -> binder; else paren term.
     2. `\` ... : in atom position, peek for `(` or `{` -> typed lambda; else
        untyped lambda with bare identifiers.

   Everything else type-checks under the typed-algebraic discipline, so the
   grammar is statically proven unambiguous along those paths. *)

(* Re-export Syntax so existing `Syntax.Surface` and `Syntax.binder` references
   continue to resolve without per-site edits.  Surface now lives in elab;
   binder is in Violet_kernel.Syntax. *)
module Syntax = struct
  include Violet_kernel.Syntax
  module Surface = Surface
end

module C : sig
  type tag =
    | T_DATA
    | T_LET
    | T_IMPORT
    | T_UNIVERSE
    | T_ARROW
    | T_COLON
    | T_LAMBDA
    | T_SLASH
    | T_VERT
    | T_JOIN
    | T_LPAREN
    | T_RPAREN
    | T_LBRACKET
    | T_RBRACKET
    | T_IDENT
    | T_EOF
    | T_WHERE
    | T_STACK_ARROW
    | T_FAT_ARROW
    | T_QMARK
    | T_OPEN
    | T_OPERATOR
    | T_SYMBOL
    | T_STRING
    | T_ELIM
    | T_INTRO
    | T_SPLIT
    | T_STRONGER_THAN
    | T_WEAKER_THAN
    | T_SAME_AS
    | T_ASSOCIATIVITY
    | T_LEFT
    | T_RIGHT
    | T_NONE
    | T_EXPORT
    | T_RECORD
    | T_DOT

  type t

  val tag_of : Lexer.token -> tag
  val empty : t
  val top : t
  val one : tag -> t
  val of_list : tag list -> t
  val union : t -> t -> t
  val inter : t -> t -> t
  val negate : t -> t
  val mem : Lexer.token -> t -> bool
  val mem_tag : tag -> t -> bool
  val is_empty : t -> bool
  val equal : t -> t -> bool
  val disjoint : t -> t -> bool
end = struct
  type tag =
    | T_DATA
    | T_LET
    | T_IMPORT
    | T_UNIVERSE
    | T_ARROW
    | T_COLON
    | T_LAMBDA
    | T_SLASH
    | T_VERT
    | T_JOIN
    | T_LPAREN
    | T_RPAREN
    | T_LBRACKET
    | T_RBRACKET
    | T_IDENT
    | T_EOF
    | T_WHERE
    | T_STACK_ARROW
    | T_FAT_ARROW
    | T_QMARK
    | T_OPEN
    | T_OPERATOR
    | T_SYMBOL
    | T_STRING
    | T_ELIM
    | T_INTRO
    | T_SPLIT
    | T_STRONGER_THAN
    | T_WEAKER_THAN
    | T_SAME_AS
    | T_ASSOCIATIVITY
    | T_LEFT
    | T_RIGHT
    | T_NONE
    | T_EXPORT
    | T_RECORD
    | T_DOT

  let tag_index = function
    | T_DATA -> 0
    | T_LET -> 1
    | T_IMPORT -> 2
    | T_UNIVERSE -> 3
    | T_ARROW -> 4
    | T_COLON -> 5
    | T_LAMBDA -> 6
    | T_VERT -> 7
    | T_JOIN -> 8
    | T_LPAREN -> 9
    | T_RPAREN -> 10
    | T_LBRACKET -> 11
    | T_RBRACKET -> 12
    | T_IDENT -> 13
    | T_EOF -> 14
    | T_WHERE -> 15
    | T_STACK_ARROW -> 16
    | T_FAT_ARROW -> 17
    | T_QMARK -> 18
    | T_SLASH -> 19
    | T_OPEN -> 20
    | T_OPERATOR -> 21
    | T_SYMBOL -> 22
    | T_STRING -> 23
    | T_ELIM -> 24
    | T_INTRO -> 25
    | T_SPLIT -> 26
    | T_STRONGER_THAN -> 27
    | T_WEAKER_THAN -> 28
    | T_SAME_AS -> 29
    | T_ASSOCIATIVITY -> 30
    | T_LEFT -> 31
    | T_RIGHT -> 32
    | T_NONE -> 33
    | T_EXPORT -> 34
    | T_RECORD -> 35
    | T_DOT -> 36
  ;;

  let tag_of : Lexer.token -> tag = function
    | Lexer.DATA -> T_DATA
    | Lexer.LET -> T_LET
    | Lexer.IMPORT -> T_IMPORT
    | Lexer.EXPORT -> T_EXPORT
    | Lexer.UNIVERSE -> T_UNIVERSE
    | Lexer.ARROW -> T_ARROW
    | Lexer.COLON -> T_COLON
    | Lexer.LAMBDA -> T_LAMBDA
    | Lexer.SLASH -> T_SLASH
    | Lexer.VERT -> T_VERT
    | Lexer.JOIN -> T_JOIN
    | Lexer.L_PAREN -> T_LPAREN
    | Lexer.R_PAREN -> T_RPAREN
    | Lexer.L_BRACKET -> T_LBRACKET
    | Lexer.R_BRACKET -> T_RBRACKET
    | Lexer.IDENT _ -> T_IDENT
    | Lexer.EOF -> T_EOF
    | Lexer.WHERE -> T_WHERE
    | Lexer.STACK_ARROW -> T_STACK_ARROW
    | Lexer.FAT_ARROW -> T_FAT_ARROW
    | Lexer.QMARK -> T_QMARK
    | Lexer.OPEN -> T_OPEN
    | Lexer.OPERATOR -> T_OPERATOR
    | Lexer.SYMBOL _ -> T_SYMBOL
    | Lexer.STRING _ -> T_STRING
    | Lexer.ELIM -> T_ELIM
    | Lexer.INTRO -> T_INTRO
    | Lexer.SPLIT -> T_SPLIT
    | Lexer.STRONGER_THAN -> T_STRONGER_THAN
    | Lexer.WEAKER_THAN -> T_WEAKER_THAN
    | Lexer.SAME_AS -> T_SAME_AS
    | Lexer.ASSOCIATIVITY -> T_ASSOCIATIVITY
    | Lexer.LEFT -> T_LEFT
    | Lexer.RIGHT -> T_RIGHT
    | Lexer.NONE -> T_NONE
    | Lexer.RECORD -> T_RECORD
    | Lexer.DOT -> T_DOT
  ;;

  type t = int

  (* 37 tags (indices 0–36) → mask of 37 bits *)
  let mask = (1 lsl 37) - 1
  let empty = 0
  let top = mask
  let one t = 1 lsl tag_index t
  let of_list ts = List.fold_left (fun s t -> s lor (1 lsl tag_index t)) 0 ts
  let union = ( lor )
  let inter = ( land )
  let negate s = lnot s land mask
  let mem_tag t s = s land (1 lsl tag_index t) <> 0
  let mem tok s = mem_tag (tag_of tok) s
  let is_empty s = s = 0
  let equal a b = a = b
  let disjoint a b = a land b = 0
end

module Tp = struct
  type t =
    { null : bool
    ; first : C.t
    ; follow : C.t
    }

  exception TypeError of string

  let tok tag = { null = false; first = C.one tag; follow = C.empty }
  let toks cs = { null = false; first = cs; follow = C.empty }
  let eps = { null = true; first = C.empty; follow = C.empty }
  let bot = { null = false; first = C.empty; follow = C.empty }

  let seq t1 t2 =
    let separate = (not t1.null) && C.disjoint t1.follow t2.first in
    if separate
    then
      { null = false
      ; first = t1.first
      ; follow = C.union t2.follow (if t2.null then t1.follow else C.empty)
      }
    else raise (TypeError "ambiguous sequencing")
  ;;

  let alt t1 t2 =
    let nonoverlapping = (not (t1.null && t2.null)) && C.disjoint t1.first t2.first in
    if nonoverlapping
    then
      { null = t1.null || t2.null
      ; first = C.union t1.first t2.first
      ; follow = C.union t1.follow t2.follow
      }
    else raise (TypeError "ambiguous alternation")
  ;;

  let equal t1 t2 =
    t1.null = t2.null && C.equal t1.first t2.first && C.equal t1.follow t2.follow
  ;;

  let fix f =
    let rec loop t =
      let t' = f t in
      if equal t t' then t' else loop t'
    in
    loop bot
  ;;
end

module P = struct
  type token_buf = Lexer.token Asai.Range.located array

  type 'a t =
    { tp : Tp.t
    ; parse : token_buf -> int -> int * 'a
    }

  exception
    ParseFailure of
      { offset : int
      ; loc : Asai.Range.t option
      ; found : Lexer.token
      }

  let fail_at buf i =
    if i < Array.length buf
    then (
      let lt = buf.(i) in
      raise
        (ParseFailure { offset = i; loc = lt.Asai.Range.loc; found = lt.Asai.Range.value }))
    else raise (ParseFailure { offset = i; loc = None; found = Lexer.EOF })
  ;;

  let tok tag =
    let parse buf i =
      if i < Array.length buf
      then (
        let lt = buf.(i) in
        if C.tag_of lt.Asai.Range.value = tag
        then i + 1, lt.Asai.Range.value
        else fail_at buf i)
      else fail_at buf i
    in
    { tp = Tp.tok tag; parse }
  ;;

  let tok_loc tag =
    let parse buf i =
      if i < Array.length buf
      then (
        let lt = buf.(i) in
        if C.tag_of lt.Asai.Range.value = tag
        then i + 1, (lt.Asai.Range.loc, lt.Asai.Range.value)
        else fail_at buf i)
      else fail_at buf i
    in
    { tp = Tp.tok tag; parse }
  ;;

  (* Wrap a parser so its result is paired with a range spanning every token
     it consumed (start of the first, end of the last). Used for top-level
     constructs so that error reports underline the entire definition rather
     than just the introducing keyword. Falls back to either endpoint's loc
     if a merged range cannot be constructed. *)
  let with_full_range p =
    let parse buf i =
      let i', x = p.parse buf i in
      let last = i' - 1 in
      let loc =
        if i < Array.length buf && last >= i && last < Array.length buf
        then
          begin match buf.(i).Asai.Range.loc, buf.(last).Asai.Range.loc with
          | Some lstart, Some lend ->
            (match Asai.Range.view lstart, Asai.Range.view lend with
             | `Range (bpos, _), `Range (_, epos) -> Some (Asai.Range.make (bpos, epos))
             | _ -> Some lstart)
          | (Some _ as l), None | None, (Some _ as l) -> l
          | None, None -> None
          end
        else None
      in
      i', (loc, x)
    in
    { tp = p.tp; parse }
  ;;

  let map f p =
    { tp = p.tp
    ; parse =
        (fun buf i ->
          let i', x = p.parse buf i in
          i', f x)
    }
  ;;

  let ( let+ ) p f = map f p

  let ( and+ ) p1 p2 =
    let parse buf i =
      let i, a = p1.parse buf i in
      let i, b = p2.parse buf i in
      i, (a, b)
    in
    { tp = Tp.seq p1.tp p2.tp; parse }
  ;;

  let ident =
    let+ t = tok C.T_IDENT in
    match t with
    | Lexer.IDENT s -> s
    | _ -> assert false
  ;;

  let ident_loc =
    let+ lv = tok_loc C.T_IDENT in
    let loc, v = lv in
    match v with
    | Lexer.IDENT s -> loc, s
    | _ -> assert false
  ;;

  let string_lit =
    let+ t = tok C.T_STRING in
    match t with
    | Lexer.STRING s -> s
    | _ -> assert false
  ;;

  let symbol =
    let+ t = tok C.T_SYMBOL in
    match t with
    | Lexer.SYMBOL s -> s
    | _ -> assert false
  ;;

  let eps = { tp = Tp.eps; parse = (fun _ i -> i, ()) }
  let fail = { tp = Tp.bot; parse = fail_at }

  let ( || ) p1 p2 =
    let tp = Tp.alt p1.tp p2.tp in
    let parse buf i =
      if i < Array.length buf
      then begin
        let t = buf.(i).Asai.Range.value in
        if C.mem t p1.tp.first
        then p1.parse buf i
        else if C.mem t p2.tp.first
        then p2.parse buf i
        else if p1.tp.null
        then p1.parse buf i
        else if p2.tp.null
        then p2.parse buf i
        else fail_at buf i
      end
      else if p1.tp.null
      then p1.parse buf i
      else if p2.tp.null
      then p2.parse buf i
      else fail_at buf i
    in
    { tp; parse }
  ;;

  let ( ==> ) p f = map f p

  let star p =
    let r = ref fail.parse in
    let recursive_tp =
      Tp.fix (fun t ->
        let body_tp = Tp.seq p.tp t in
        Tp.alt Tp.eps body_tp)
    in
    let recursive = { tp = recursive_tp; parse = (fun buf i -> !r buf i) } in
    let body =
      (eps ==> fun () -> [])
      || let+ x = p
         and+ xs = recursive in
         x :: xs
    in
    r := body.parse;
    body
  ;;

  let fix f =
    let g t = (f { fail with tp = t }).tp in
    let r = ref fail.parse in
    let p = f { tp = Tp.fix g; parse = (fun buf i -> !r buf i) } in
    r := p.parse;
    p
  ;;

  let parse p = p.parse
end

module Grammar = struct
  open P
  module S = Syntax.Surface

  let wrap_loc loc v =
    match loc with
    | Some l -> S.Located (Asai.Range.locate l v)
    | None -> v
  ;;

  let p_qname : string list t =
    let+ first = ident
    and+ rest =
      star
        (let+ _ = tok C.T_SLASH
         and+ x = ident in
         x)
    in
    first :: rest
  ;;

  let p_import : string list t =
    let+ _ = tok C.T_IMPORT
    and+ path = p_qname in
    path
  ;;

  let p_export : string list t =
    let+ _ = tok C.T_EXPORT
    and+ first = ident
    and+ rest = star ident in
    first :: rest
  ;;

  (* Peek helpers used by the two hand-coded disambiguators. *)
  let peek_is_binder_after_lparen (buf : P.token_buf) (i : int) : bool =
    (* `(` at i ; check whether i+1.. is `IDENT+ :` *)
    let n = Array.length buf in
    if i + 1 >= n
    then false
    else if C.tag_of buf.(i + 1).Asai.Range.value <> C.T_IDENT
    then false
    else begin
      let j = ref (i + 1) in
      while !j < n && C.tag_of buf.(!j).Asai.Range.value = C.T_IDENT do
        incr j
      done;
      !j < n && C.tag_of buf.(!j).Asai.Range.value = C.T_COLON
    end
  ;;

  let peek_is_typed_lambda (buf : P.token_buf) (i : int) : bool =
    (* `\` at i ; typed iff next is `(` or `{` *)
    let n = Array.length buf in
    if i + 1 >= n
    then false
    else (
      match C.tag_of buf.(i + 1).Asai.Range.value with
      | C.T_LPAREN | C.T_LBRACKET -> true
      | _ -> false)
  ;;

  (* Three-way classifier for `{` at position i in the token buffer.
     Returns:
       `Binder  — `{name... : type} -> body`
       `Literal — `{ field = e, … }` or `{ x }` (pun) or `{}`
       `Update  — `{ expr | field = e, … }` copy-with-update

     Strategy: scan forward from i+1, balancing L_BRACKET/L_PAREN depth,
     until we find a token at depth 0 that disambiguates:
       VERT (`|`)  → Update
       R_BRACKET (`}`) at depth 0 → Literal (empty or single pun ending)
       SYMBOL "=" → Literal (explicit field)
       SYMBOL "," → Literal (pun list)
       COLON      → Binder
       EOF / other → Binder (let downstream fail)
  *)
  type lbrace_kind =
    | Binder
    | Literal
    | Update

  let classify_lbrace (buf : P.token_buf) (i : int) : lbrace_kind =
    let n = Array.length buf in
    (* i points at `{`; start scanning from i+1 *)
    let depth = ref 0 in
    let j = ref (i + 1) in
    let result = ref None in
    while !result = None && !j < n do
      let tok = buf.(!j).Asai.Range.value in
      (match tok with
       | Lexer.L_BRACKET | Lexer.L_PAREN -> incr depth
       | Lexer.R_BRACKET | Lexer.R_PAREN ->
         if !depth = 0
         then result := Some Literal (* closing `}` at depth 0 → literal *)
         else decr depth
       | Lexer.VERT when !depth = 0 -> result := Some Update
       | Lexer.COLON when !depth = 0 -> result := Some Binder
       | Lexer.SYMBOL "=" when !depth = 0 -> result := Some Literal
       | Lexer.SYMBOL "," when !depth = 0 -> result := Some Literal
       | _ -> ());
      incr j
    done;
    match !result with
    | Some k -> k
    | None -> Binder (* ran off end — let downstream fail *)
  ;;

  let peek_is_record_lit (buf : P.token_buf) (i : int) : bool =
    classify_lbrace buf i = Literal
  ;;

  let peek_is_record_update (buf : P.token_buf) (i : int) : bool =
    classify_lbrace buf i = Update
  ;;

  (* The whole preterm grammar, including the two hybrid disambiguation
     points. Tied together by a single `fix`. *)
  let p_term : S.preterm t =
    fix (fun term ->
      (* `IDENT+` — at least one ident, returns the name list *)
      let p_idents : string list t =
        let+ first = ident
        and+ rest = star ident in
        first :: rest
      in
      let mk_binding implicit names bound : S.preterm Syntax.binder list =
        List.map (fun name -> { Syntax.name = Syntax.Named name; bound; implicit }) names
      in
      let p_binding_parens : S.preterm Syntax.binder list t =
        let+ _ = tok C.T_LPAREN
        and+ names = p_idents
        and+ _ = tok C.T_COLON
        and+ ty = term
        and+ _ = tok C.T_RPAREN in
        mk_binding false names ty
      in
      let p_binding_brackets : S.preterm Syntax.binder list t =
        let+ _ = tok C.T_LBRACKET
        and+ names = p_idents
        and+ _ = tok C.T_COLON
        and+ ty = term
        and+ _ = tok C.T_RBRACKET in
        mk_binding true names ty
      in
      let p_binding = p_binding_parens || p_binding_brackets in
      let p_bindings_flat =
        let+ groups = star p_binding in
        List.concat groups
      in
      (* atoms *)
      let ident_atom : S.preterm t =
        let+ loc, first = ident_loc
        and+ rest =
          star
            (let+ _ = tok C.T_SLASH
             and+ x = ident in
             x)
        in
        wrap_loc loc (S.Var (first :: rest))
      in
      (* LPAREN atom: disambiguate binder vs paren-term via 2-token peek *)
      let parens_binder_atom : S.preterm t =
        let+ binders = p_binding_parens
        and+ _ = tok C.T_ARROW
        and+ rhs = term in
        S.pi binders rhs
      in
      let parens_term_atom : S.preterm t =
        let+ loc, _ = tok_loc C.T_LPAREN
        and+ inner = term
        and+ _ = tok C.T_RPAREN in
        wrap_loc loc inner
      in
      let p_atom_lparen : S.preterm t =
        let tp = Tp.{ null = false; first = C.one C.T_LPAREN; follow = C.empty } in
        let parse buf i =
          if peek_is_binder_after_lparen buf i
          then parens_binder_atom.parse buf i
          else parens_term_atom.parse buf i
        in
        { tp; parse }
      in
      (* LBRACKET atom: always implicit binder `{x:T}+ -> body` *)
      let p_atom_lbracket : S.preterm t =
        let+ binders = p_binding_brackets
        and+ _ = tok C.T_ARROW
        and+ rhs = term in
        S.pi binders rhs
      in
      (* LAMBDA atom: untyped (`\ x y -> body`) or typed (`\ (x:T) -> body`) *)
      let lambda_untyped : S.preterm t =
        let+ _ = tok C.T_LAMBDA
        and+ names = p_idents
        and+ _ = tok C.T_ARROW
        and+ body = term in
        S.lambda names body
      in
      let lambda_typed : S.preterm t =
        let+ _ = tok C.T_LAMBDA
        and+ binders = p_bindings_flat
        and+ _ = tok C.T_ARROW
        and+ body = term in
        S.typed_lambda binders body
      in
      let p_atom_lambda : S.preterm t =
        let tp = Tp.{ null = false; first = C.one C.T_LAMBDA; follow = C.empty } in
        let parse buf i =
          if peek_is_typed_lambda buf i
          then lambda_typed.parse buf i
          else lambda_untyped.parse buf i
        in
        { tp; parse }
      in
      (* QMARK atom: `?` optionally followed by an IDENT that is IMMEDIATELY
         adjacent (no whitespace gap). The `tp.first` is only T_QMARK, so the
         dispatcher in `||` only enters here when the current token IS a QMARK.
         If there's a space between `?` and the next IDENT, the IDENT is left
         for the surrounding `spine` to consume as a separate argument. *)
      let goal_atom : S.preterm t =
        let tp = Tp.{ null = false; first = C.one C.T_QMARK; follow = C.empty } in
        let parse buf i =
          let qmark_loc = buf.(i).Asai.Range.loc in
          let after = i + 1 in
          let adjacent_ident =
            after < Array.length buf
            && C.tag_of buf.(after).Asai.Range.value = C.T_IDENT
            &&
            match qmark_loc, buf.(after).Asai.Range.loc with
            | Some q, Some j ->
              (match Asai.Range.view q, Asai.Range.view j with
               | `Range (_, q_end), `Range (j_start, _) -> q_end.offset = j_start.offset
               | _ -> false)
            | _ -> false
          in
          if adjacent_ident
          then (
            match buf.(after).Asai.Range.value with
            | Lexer.IDENT s ->
              let ident_loc = buf.(after).Asai.Range.loc in
              let span =
                match qmark_loc, ident_loc with
                | Some q, Some j ->
                  (match Asai.Range.view q, Asai.Range.view j with
                   | `Range (bpos, _), `Range (_, epos) ->
                     Some (Asai.Range.make (bpos, epos))
                   | _ -> qmark_loc)
                | Some _, None -> qmark_loc
                | None, _ -> ident_loc
              in
              after + 1, wrap_loc span (S.Goal (Some s))
            | _ -> assert false)
          else after, wrap_loc qmark_loc (S.Goal None)
        in
        { tp; parse }
      in
      (* `atom_no_bracket` covers all single-token structural forms PLUS bare
         identifiers, but excludes {…}-forms.  Used as Var atoms in soup
         positions and as the building block for record-entry values. *)
      let atom_no_bracket : S.preterm t =
        ident_atom || goal_atom || p_atom_lparen || p_atom_lambda
      in
      (* RECORD LITERAL: `{ field = expr , … }` or `{ field , … }` (pun) or `{}`.
         All variants start with T_LBRACKET.  Disambiguation from the binder form
         `{x : T} -> body` is done by peek_is_record_lit.

         `=` and `,` are both SYMBOL tokens in this lexer.  To prevent the full
         term parser from consuming commas (which are part of the record separator
         syntax) as operator soup tokens, record field values are parsed with a
         *restricted* parser (p_record_value) that collects `atom_no_bracket`
         items in a loop, stopping before any SYMBOL or R_BRACKET token.  Lbracket
         forms ({…}) inside field values must be parenthesised. *)
      (* Parse a record-entry value: a non-empty sequence of atom_no_bracket
         items forming an application spine.  Stops before SYMBOL tokens (which
         include "," and "=") and R_BRACKET.  Returns Op_soup for multi-item
         spines, or unwraps single-item ones. *)
      let p_record_value : S.preterm t =
        let tp =
          Tp.
            { null = false
            ; first = C.of_list [ C.T_IDENT; C.T_QMARK; C.T_LPAREN; C.T_LAMBDA ]
            ; follow = C.empty
            }
        in
        let parse buf i =
          let n = Array.length buf in
          (* Greedily consume `.field` projections after an atom, mirroring the
             postfix `proj_soup` loop in the full term parser.  Without this,
             writing `{ fst = p.fst }` would fail to parse because the restricted
             field-value loop doesn't include the projection layer. *)
          let apply_proj_loop start_i base =
            let acc = ref base in
            let pos = ref start_i in
            let continue_ = ref true in
            while
              !continue_ && !pos < n && C.tag_of buf.(!pos).Asai.Range.value = C.T_DOT
            do
              let dot_i = !pos + 1 in
              if dot_i < n && C.tag_of buf.(dot_i).Asai.Range.value = C.T_IDENT
              then begin
                let field =
                  match buf.(dot_i).Asai.Range.value with
                  | Lexer.IDENT s -> s
                  | _ -> assert false
                in
                acc := S.Proj (!acc, field);
                pos := dot_i + 1
              end
              else continue_ := false
            done;
            !pos, !acc
          in
          (* Parse one atom_no_bracket item (with trailing `.field*`); returns
             None when no more. *)
          let parse_item buf i =
            if i >= n
            then None
            else (
              match C.tag_of buf.(i).Asai.Range.value with
              | C.T_IDENT | C.T_QMARK | C.T_LPAREN | C.T_LAMBDA ->
                let i, a = atom_no_bracket.parse buf i in
                let i, a = apply_proj_loop i a in
                Some (i, a)
              | _ -> None)
          in
          match parse_item buf i with
          | None -> P.fail_at buf i
          | Some (i, first_atom) ->
            let atoms = ref [ first_atom ] in
            let pos = ref i in
            let continue_ = ref true in
            while !continue_ do
              match parse_item buf !pos with
              | None -> continue_ := false
              | Some (i', a) ->
                atoms := a :: !atoms;
                pos := i'
            done;
            let result =
              match List.rev !atoms with
              | [ a ] -> a
              | parts -> S.Op_soup (List.map (fun a -> S.SI_Atom a) parts)
            in
            !pos, result
        in
        { tp; parse }
      in
      (* One field entry: `name = value` (explicit) or `name` (pun). *)
      let p_record_entry : (string * S.preterm) t =
        let tp = Tp.{ null = false; first = C.one C.T_IDENT; follow = C.empty } in
        let parse buf i =
          let i, name_tok = (tok C.T_IDENT).parse buf i in
          let name =
            match name_tok with
            | Lexer.IDENT s -> s
            | _ -> assert false
          in
          if i < Array.length buf
          then (
            match buf.(i).Asai.Range.value with
            | Lexer.SYMBOL "=" ->
              let i = i + 1 in
              let i, e = p_record_value.parse buf i in
              i, (name, e)
            | _ -> i, (name, S.Var [ name ]))
          else i, (name, S.Var [ name ])
        in
        { tp; parse }
      in
      (* `{ entry , … }` or `{}`. `,` is SYMBOL "," so we hand-code the loop. *)
      let p_record_lit : S.preterm t =
        let tp = Tp.{ null = false; first = C.one C.T_LBRACKET; follow = C.empty } in
        let parse buf i =
          let i = i + 1 in
          (* consume `{` *)
          let n = Array.length buf in
          if i < n && C.tag_of buf.(i).Asai.Range.value = C.T_RBRACKET
          then i + 1, S.RecordLit [] (* `{}` *)
          else begin
            let i, first = p_record_entry.parse buf i in
            let entries = ref [ first ] in
            let pos = ref i in
            while
              !pos < n
              &&
              match buf.(!pos).Asai.Range.value with
              | Lexer.SYMBOL "," -> true
              | _ -> false
            do
              pos := !pos + 1;
              (* skip `,` *)
              let i', e = p_record_entry.parse buf !pos in
              entries := e :: !entries;
              pos := i'
            done;
            let i', _ = (tok C.T_RBRACKET).parse buf !pos in
            i', S.RecordLit (List.rev !entries)
          end
        in
        { tp; parse }
      in
      (* `{ expr | entry , … }` copy-with-update.
         The base expression is parsed with `p_record_value` (the same
         restricted spine parser used for field values), which stops before
         SYMBOL tokens — including `|` — and R_BRACKET.  This means the base
         must be a simple application spine of atoms (no infix operators),
         which is the common case; more complex bases can be parenthesised. *)
      let p_record_update : S.preterm t =
        let tp = Tp.{ null = false; first = C.one C.T_LBRACKET; follow = C.empty } in
        let parse buf i =
          let i = i + 1 in
          (* consume `{` *)
          let n = Array.length buf in
          (* Parse the base expression: a spine of atom_no_bracket items,
             stopping before VERT or R_BRACKET. *)
          let i, base = p_record_value.parse buf i in
          (* Consume `|` (T_VERT) *)
          let i, _ = (tok C.T_VERT).parse buf i in
          (* Parse comma-separated entries *)
          if i < n && C.tag_of buf.(i).Asai.Range.value = C.T_RBRACKET
          then
            (* `{ base | }` — zero update fields; unusual but valid *)
            i + 1, S.RecordUpdate (base, [])
          else begin
            let i, first = p_record_entry.parse buf i in
            let entries = ref [ first ] in
            let pos = ref i in
            while
              !pos < n
              &&
              match buf.(!pos).Asai.Range.value with
              | Lexer.SYMBOL "," -> true
              | _ -> false
            do
              pos := !pos + 1;
              (* skip `,` *)
              let i', e = p_record_entry.parse buf !pos in
              entries := e :: !entries;
              pos := i'
            done;
            let i', _ = (tok C.T_RBRACKET).parse buf !pos in
            i', S.RecordUpdate (base, List.rev !entries)
          end
        in
        { tp; parse }
      in
      (* Disambiguating T_LBRACKET atom: record update, record literal, OR
         implicit-binder pi.  All start with `{`; we use the 3-way classifier
         to decide which form is intended.  Update is tried first because
         `{ ident | …` cannot be distinguished from `{ ident = …` until the
         second token after the ident. *)
      let p_lbracket_atom : S.preterm t =
        let tp = Tp.{ null = false; first = C.one C.T_LBRACKET; follow = C.empty } in
        let parse buf i =
          if peek_is_record_update buf i
          then p_record_update.parse buf i
          else if peek_is_record_lit buf i
          then p_record_lit.parse buf i
          else p_atom_lbracket.parse buf i
        in
        { tp; parse }
      in
      (* `atom` extends atom_no_bracket with lbracket forms (record literal or
         implicit-binder pi).  Used inside soup tails for `{ atom }` implicit args. *)
      let atom : S.preterm t = atom_no_bracket || p_lbracket_atom in
      (* Structural soup atoms: paren-term, lambda, hole/goal, and the
         binder form `{x:T} -> body`. IDENT and SYMBOL are NOT here — they
         become SI_Name and are interpreted by the resolver. *)
      let structural_atom_no_lbracket : S.preterm t =
        goal_atom || p_atom_lparen || p_atom_lambda
      in
      (* SYMBOL token as a name. *)
      let p_symbol_name : string t = symbol in
      (* IDENT, optionally followed by `/`-separated continuation segments.
         A bare ident becomes SI_Name (so it can match operator literals);
         a qualified name like `Nat/suc` becomes SI_Atom (Var [...]) since
         qualified names are never operator tokens. *)
      let p_ident_soup_item : S.soup_item t =
        let+ loc, first = ident_loc
        and+ rest =
          star
            (let+ _ = tok C.T_SLASH
             and+ x = ident in
             x)
        in
        match rest with
        | [] -> S.SI_Name first
        | _ -> S.SI_Atom (wrap_loc loc (S.Var (first :: rest)))
      in
      (* Soup-head item. First sets: T_IDENT, T_SYMBOL, T_QMARK, T_LPAREN,
         T_LAMBDA, T_LBRACKET — disjoint.
         T_LBRACKET uses the disambiguating p_lbracket_atom (record literal
         OR implicit-binder pi). *)
      let soup_head_item : S.soup_item t =
        p_ident_soup_item
        || (let+ n = p_symbol_name in
            S.SI_Name n)
        || (let+ a = structural_atom_no_lbracket in
            S.SI_Atom a)
        ||
        let+ a = p_lbracket_atom in
        S.SI_Atom a
      in
      (* Soup-tail item. In tail position, `{...}` is ALWAYS an implicit
         argument (`{ atom }`); the binder form is illegal here. First sets
         disjoint with each other. *)
      let soup_tail_item : S.soup_item t =
        p_ident_soup_item
        || (let+ n = p_symbol_name in
            S.SI_Name n)
        || (let+ a = structural_atom_no_lbracket in
            S.SI_Atom a)
        ||
        let+ _ = tok C.T_LBRACKET
        and+ a = atom
        and+ _ = tok C.T_RBRACKET in
        S.SI_Imp_arg a
      in
      (* A single op-soup: one head followed by zero-or-more tail items. *)
      let op_soup : S.preterm t =
        let+ head = soup_head_item
        and+ rest = star soup_tail_item in
        S.Op_soup (head :: rest)
      in
      (* Postfix `.field` projection loop.  After parsing an op-soup we
         greedily consume `T_DOT IDENT` sequences and wrap the accumulator
         in `S.Proj`.  This produces left-associative chains:
             r.x.y  ⟹  Proj(Proj(r,"x"),"y")
         Hand-coded because the typed-algebraic `star` combinator would need
         the recursion to be expressed through `fix`, but this imperative
         loop is simpler and correct. *)
      let proj_soup : S.preterm t =
        let tp = op_soup.tp in
        let parse buf i =
          let i, base = op_soup.parse buf i in
          let n = Array.length buf in
          let acc = ref base in
          let pos = ref i in
          let continue_ = ref true in
          while
            !continue_ && !pos < n && C.tag_of buf.(!pos).Asai.Range.value = C.T_DOT
          do
            (* Peek that the next token after DOT is an IDENT. *)
            let dot_i = !pos + 1 in
            if dot_i < n && C.tag_of buf.(dot_i).Asai.Range.value = C.T_IDENT
            then begin
              let field_tok = buf.(dot_i).Asai.Range.value in
              let field =
                match field_tok with
                | Lexer.IDENT s -> s
                | _ -> assert false
              in
              acc := S.Proj (!acc, field);
              pos := dot_i + 1
            end
            else continue_ := false
          done;
          !pos, !acc
        in
        { tp; parse }
      in
      (* `max_level: proj_soup ('⊔' proj_soup)*`, right-associative as before. *)
      let max_level : S.preterm t =
        let+ head = proj_soup
        and+ tail =
          star
            (let+ _ = tok C.T_JOIN
             and+ s = proj_soup in
             s)
        in
        match List.rev (head :: tail) with
        | [] -> assert false
        | last :: rev_rest -> List.fold_left (fun acc x -> S.Max (x, acc)) last rev_rest
      in
      let opt_arrow : S.preterm option t =
        (eps ==> fun () -> None)
        ||
        let+ _ = tok C.T_ARROW
        and+ rhs = term in
        Some rhs
      in
      let+ lhs = max_level
      and+ rhs = opt_arrow in
      match rhs with
      | None -> lhs
      | Some r -> S.Pi ({ name = Syntax.Anon; bound = lhs; implicit = false }, r))
  ;;

  let p_idents : string list t =
    let+ first = ident
    and+ rest = star ident in
    first :: rest
  ;;

  let p_binding_parens : S.preterm Syntax.binder list t =
    let+ _ = tok C.T_LPAREN
    and+ names = p_idents
    and+ _ = tok C.T_COLON
    and+ ty = p_term
    and+ _ = tok C.T_RPAREN in
    List.map
      (fun name -> { Syntax.name = Syntax.Named name; bound = ty; implicit = false })
      names
  ;;

  let p_binding_brackets : S.preterm Syntax.binder list t =
    let+ _ = tok C.T_LBRACKET
    and+ names = p_idents
    and+ _ = tok C.T_COLON
    and+ ty = p_term
    and+ _ = tok C.T_RBRACKET in
    List.map
      (fun name -> { Syntax.name = Syntax.Named name; bound = ty; implicit = true })
      names
  ;;

  let p_binding = p_binding_parens || p_binding_brackets

  let p_bindings_flat : S.preterm Syntax.binder list t =
    let+ groups = star p_binding in
    List.concat groups
  ;;

  let p_ctor : S.pretype Syntax.binder t =
    let+ _ = tok C.T_VERT
    and+ name = ident
    and+ _ = tok C.T_COLON
    and+ ty = p_term in
    { Syntax.name = Syntax.Named name; bound = ty; implicit = false }
  ;;

  let p_stack_move : S.stack_move t =
    let+ _ = tok C.T_STACK_ARROW
    and+ move =
      (let+ _ = tok C.T_INTRO in
       S.Intro)
      ||
      let+ _ = tok C.T_SPLIT in
      S.Split
    in
    move
  ;;

  (* peek_is_record_pattern: returns true when the token at position i is `{`
     and the next two tokens are `IDENT SYMBOL "="`.
     This distinguishes `{ fst = a, … }` (PRecord) from `{name}` (PImpVar). *)
  let peek_is_record_pattern (buf : P.token_buf) (i : int) : bool =
    let n = Array.length buf in
    if i + 2 >= n
    then false
    else (
      match
        ( buf.(i).Asai.Range.value
        , buf.(i + 1).Asai.Range.value
        , buf.(i + 2).Asai.Range.value )
      with
      | Lexer.L_BRACKET, Lexer.IDENT _, Lexer.SYMBOL "=" -> true
      | _ -> false)
  ;;

  (* p_pattern: parses a single pattern (PVar, PCon, PImpVar, PRecord).
     Uses a ref so that the p_lbrace arm can call back into p_pattern for
     PRecord sub-patterns without triggering eager OCaml let-rec issues. *)
  let p_pattern : S.pattern t =
    (* ref stub — filled in below *)
    let self_ref : (P.token_buf -> int -> int * S.pattern) ref =
      ref (fun buf i -> P.fail_at buf i)
    in
    let self_tp =
      (* first-set: IDENT | T_LPAREN | T_LBRACKET *)
      Tp.
        { null = false
        ; first = C.of_list [ C.T_IDENT; C.T_LPAREN; C.T_LBRACKET ]
        ; follow = C.empty
        }
    in
    let self : S.pattern t = { tp = self_tp; parse = (fun buf i -> !self_ref buf i) } in
    (* PVar / PWildcard: an IDENT. A literal `_` is a wildcard pattern that
       binds nothing referenceable; any other identifier binds a variable. *)
    let p_var =
      let+ name = ident in
      if String.equal name "_" then S.PWildcard else S.PVar name
    in
    (* PCon: `( ctor arg… )` where each arg is itself a pattern (so
       `(cons n1 (cons n2 stk))` works). *)
    let p_con =
      let+ _ = tok C.T_LPAREN
      and+ ctor = ident
      and+ vs = star self
      and+ _ = tok C.T_RPAREN in
      S.PCon (ctor, vs)
    in
    (* p_lbrace: disambiguates `{…}` — PRecord vs PImpVar *)
    let p_lbrace : S.pattern t =
      let tp = Tp.{ null = false; first = C.one C.T_LBRACKET; follow = C.empty } in
      let parse buf i =
        if peek_is_record_pattern buf i
        then begin
          (* PRecord: `{ name = pat , … }` — no punning allowed *)
          let i = i + 1 in
          (* consume `{` *)
          let n = Array.length buf in
          let parse_entry pos =
            let pos, name_tok = (tok C.T_IDENT).parse buf pos in
            let name =
              match name_tok with
              | Lexer.IDENT s -> s
              | _ -> assert false
            in
            (* Require `=` — punning is forbidden in patterns *)
            let pos =
              if pos < n
              then (
                match buf.(pos).Asai.Range.value with
                | Lexer.SYMBOL "=" -> pos + 1
                | _ -> (P.fail_at buf pos : int))
              else (P.fail_at buf pos : int)
            in
            let pos, p = self.parse buf pos in
            pos, (name, p)
          in
          if i < n && C.tag_of buf.(i).Asai.Range.value = C.T_RBRACKET
          then i + 1, S.PRecord []
          else begin
            let i, first = parse_entry i in
            let entries = ref [ first ] in
            let pos = ref i in
            while
              !pos < n
              &&
              match buf.(!pos).Asai.Range.value with
              | Lexer.SYMBOL "," -> true
              | _ -> false
            do
              pos := !pos + 1;
              (* skip `,` *)
              let i', e = parse_entry !pos in
              entries := e :: !entries;
              pos := i'
            done;
            let i', _ = (tok C.T_RBRACKET).parse buf !pos in
            i', S.PRecord (List.rev !entries)
          end
        end
        else begin
          (* PImpVar: `{ name }` *)
          let i = i + 1 in
          (* consume `{` *)
          let i, name_tok = (tok C.T_IDENT).parse buf i in
          let name =
            match name_tok with
            | Lexer.IDENT s -> s
            | _ -> assert false
          in
          let i, _ = (tok C.T_RBRACKET).parse buf i in
          i, S.PImpVar name
        end
      in
      { tp; parse }
    in
    let body = p_var || p_con || p_lbrace in
    self_ref := body.parse;
    body
  ;;

  let p_clause : S.clause t =
    let+ _ = tok C.T_VERT
    and+ head = ident
    and+ patterns = star p_pattern
    and+ body =
      (let+ _ = tok C.T_FAT_ARROW
       and+ tm = p_term in
       tm)
      ||
      let+ _ = tok C.T_STACK_ARROW
      and+ _ = tok C.T_ELIM
      and+ target = ident in
      S.Inline_elim { target; siblings = []; outer_subst = []; target_override = None }
    in
    { S.head; patterns; body }
  ;;

  type elim_header_data =
    { head : string
    ; intros : (string * bool) list
    ; target : string
    }

  let p_intro_atom : (string * bool) t =
    (let+ name = ident in
     name, false)
    ||
    let+ _ = tok C.T_LBRACKET
    and+ name = ident
    and+ _ = tok C.T_RBRACKET in
    name, true
  ;;

  let p_elim_header : elim_header_data t =
    let+ head = ident
    and+ intros = star p_intro_atom
    and+ _ = tok C.T_STACK_ARROW
    and+ _ = tok C.T_ELIM
    and+ target = ident in
    { head; intros; target }
  ;;

  type where_head =
    | WH_Elim of elim_header_data
    | WH_Moves of S.stack_move list

  type let_body =
    | LB_Assign of S.preterm
    | LB_Where of S.stack_move list * S.clause list
    | LB_Elim of string list * elim_header_data * S.clause list

  let p_open_clause : string t =
    let+ _ = tok C.T_OPEN
    and+ name = ident in
    name
  ;;

  let p_let_body : let_body t =
    (let+ _ = tok C.T_FAT_ARROW
     and+ tm = p_term in
     LB_Assign tm)
    ||
    let+ _ = tok C.T_WHERE
    and+ opens = star p_open_clause
    and+ wh =
      (let+ hdr = p_elim_header in
       WH_Elim hdr)
      ||
      let+ moves = star p_stack_move in
      WH_Moves moves
    and+ clauses = star p_clause in
    match wh with
    | WH_Elim hdr -> LB_Elim (opens, hdr, clauses)
    | WH_Moves moves ->
      if opens <> []
      then
        Reporter.fatalf
          Parse_error
          "`open` clauses are only supported inside `elim`-style `where` blocks";
      LB_Where (moves, clauses)
  ;;

  let p_let_top : S.top Asai.Range.located t =
    let+ loc, (name, bindings, ty, body) =
      with_full_range
        (let+ _ = tok C.T_LET
         and+ name = ident
         and+ bindings = p_bindings_flat
         and+ _ = tok C.T_COLON
         and+ ty = p_term
         and+ body = p_let_body in
         name, bindings, ty, body)
    in
    match body with
    | LB_Assign tm -> { Asai.Range.loc; value = S.Let (name, bindings, ty, tm) }
    | LB_Where (moves, clauses) ->
      { Asai.Range.loc
      ; value = S.Stack_def { name; params = bindings; signature = ty; moves; clauses }
      }
    | LB_Elim (opens, { head; intros; target }, clauses) ->
      if not (String.equal head name)
      then
        Reporter.fatalf
          Parse_error
          "elim-header head `%s` must match let name `%s`"
          head
          name;
      { Asai.Range.loc
      ; value =
          S.Elim_def
            { name; params = bindings; signature = ty; opens; intros; target; clauses }
      }
  ;;

  let p_data_top : S.top Asai.Range.located t =
    let+ loc, (name, params, ret, ctors) =
      with_full_range
        (let+ _ = tok C.T_DATA
         and+ name = ident
         and+ params = p_bindings_flat
         and+ _ = tok C.T_COLON
         and+ ret = p_term
         and+ ctors = star p_ctor in
         name, params, ret, ctors)
    in
    let value =
      S.Data { name; params; deps = S.telescope ret; ind_ty = S.codomain ret; ctors }
    in
    { Asai.Range.loc; value }
  ;;

  let p_record_field : S.pretype Syntax.binder t =
    let+ _ = tok C.T_VERT
    and+ name = ident
    and+ _ = tok C.T_COLON
    and+ ty = p_term in
    { Syntax.name = Syntax.Named name; bound = ty; implicit = false }
  ;;

  let p_record_top : S.top Asai.Range.located t =
    let+ loc, (name, params, ret, fields) =
      with_full_range
        (let+ _ = tok C.T_RECORD
         and+ name = ident
         and+ params = p_bindings_flat
         and+ _ = tok C.T_COLON
         and+ ret = p_term
         and+ fields = star p_record_field in
         name, params, ret, fields)
    in
    let value = S.Record { name; params; ind_ty = ret; fields } in
    { Asai.Range.loc; value }
  ;;

  let p_universe_top : S.top Asai.Range.located t =
    let+ loc, names =
      with_full_range
        (let+ _ = tok C.T_UNIVERSE
         and+ first = ident
         and+ rest = star ident in
         first :: rest)
    in
    { Asai.Range.loc; value = S.Universe_decl names }
  ;;

  (* A "name path" referencing another operator in `\weaker_than:` / etc.
     Consumes a maximal run of consecutive IDENT and SYMBOL tokens. Stops at
     anything else (backslash keyword, top keyword, EOF). At least one token. *)
  let p_name_path : S.op_name_path P.t =
    let tp =
      Tp.{ null = false; first = C.of_list [ C.T_IDENT; C.T_SYMBOL ]; follow = C.empty }
    in
    let parse buf i =
      let n = Array.length buf in
      let rec loop i acc =
        if i < n
        then
          begin match buf.(i).Asai.Range.value with
          | Lexer.IDENT s -> loop (i + 1) (s :: acc)
          | Lexer.SYMBOL s -> loop (i + 1) (s :: acc)
          | _ -> i, List.rev acc
          end
        else i, List.rev acc
      in
      let i', path = loop i [] in
      match path with
      | [] -> P.fail_at buf i
      | _ -> i', path
    in
    { tp; parse }
  ;;

  (* One operator option. Hand-coded because the value-level dispatch on the
     specific keyword token (`\weaker_than` vs `\stronger_than` vs ...) doesn't
     fit the static FIRST-set discipline of `||`. *)
  let p_op_option : S.op_option P.t =
    let tp =
      Tp.
        { null = false
        ; first =
            C.of_list
              [ C.T_STRONGER_THAN; C.T_WEAKER_THAN; C.T_SAME_AS; C.T_ASSOCIATIVITY ]
        ; follow = C.empty
        }
    in
    let parse buf i =
      let n = Array.length buf in
      if i >= n then P.fail_at buf i;
      let kw_tok = buf.(i) in
      let kw = C.tag_of kw_tok.Asai.Range.value in
      let i = i + 1 in
      let i, _ = (tok C.T_COLON).parse buf i in
      match kw with
      | C.T_WEAKER_THAN ->
        let i, path = p_name_path.parse buf i in
        i, S.OO_Weaker_than [ path ]
      | C.T_STRONGER_THAN ->
        let i, path = p_name_path.parse buf i in
        i, S.OO_Stronger_than [ path ]
      | C.T_SAME_AS ->
        let i, path = p_name_path.parse buf i in
        i, S.OO_Same_as [ path ]
      | C.T_ASSOCIATIVITY ->
        if i >= n then P.fail_at buf i;
        let a =
          match C.tag_of buf.(i).Asai.Range.value with
          | C.T_LEFT -> S.OA_Left
          | C.T_RIGHT -> S.OA_Right
          | C.T_NONE -> S.OA_None
          | _ ->
            Reporter.fatalf
              ?loc:buf.(i).Asai.Range.loc
              Parse_error
              "expected `\\left`, `\\right`, or `\\none` after `\\associativity:`"
        in
        i + 1, S.OO_Associativity a
      | _ ->
        Reporter.fatalf
          ?loc:kw_tok.Asai.Range.loc
          Parse_error
          "expected one of \\weaker_than, \\stronger_than, \\same_as, \\associativity"
    in
    { tp; parse }
  ;;

  let p_operator_top : S.top Asai.Range.located t =
    let+ loc, (template, body, options) =
      with_full_range
        (let+ _ = tok C.T_OPERATOR
         and+ template = string_lit
         and+ _ = tok C.T_FAT_ARROW
         and+ body = p_term
         and+ options = star p_op_option in
         template, body, options)
    in
    { Asai.Range.loc; value = S.Operator_decl { template; body; options } }
  ;;

  let p_top : S.top Asai.Range.located t =
    p_let_top || p_data_top || p_record_top || p_operator_top
  ;;

  let p_tops_loop : S.top Asai.Range.located list t =
    fix (fun self ->
      (let+ t = p_top
       and+ rest = self in
       t :: rest)
      || let+ _ = tok C.T_EOF in
         [])
  ;;

  let p_module_named (name : string) : S.t t =
    let body =
      let+ tops = p_tops_loop in
      { S.name; imports = []; exports = []; tops }
    in
    fix (fun self ->
      (let+ i = p_import
       and+ rest = self in
       { rest with S.imports = i :: rest.S.imports })
      || (let+ ns = p_export
          and+ rest = self in
          { rest with S.exports = ns @ rest.S.exports })
      || (let+ u = p_universe_top
          and+ rest = self in
          { rest with S.tops = u :: rest.S.tops })
      || body)
  ;;
end

let rec tokens filename lexbuf =
  let tok = Lexer.token lexbuf in
  let loc = Asai.Range.of_lexbuf ~source:(`File filename) lexbuf in
  match tok with
  | Lexer.EOF -> [ Asai.Range.locate loc tok ]
  | _ -> Asai.Range.locate loc tok :: tokens filename lexbuf
;;

let parse_buf ~name buf =
  match P.parse (Grammar.p_module_named name) buf 0 with
  | _, m ->
    let seen = Hashtbl.create 16 in
    List.iter
      (fun nm ->
         if Hashtbl.mem seen nm
         then Reporter.fatalf Export_error "duplicate name in \\export: `%s`" nm
         else Hashtbl.add seen nm ())
      m.Surface.exports;
    m
  | exception P.ParseFailure { offset; loc; found } ->
    (match loc with
     | Some loc ->
       Reporter.fatalf
         ~loc
         Parse_error
         "unexpected token `%s` at offset %d"
         ([%show: Lexer.token] found)
         offset
     | None ->
       Reporter.fatalf
         Parse_error
         "unexpected token `%s` at offset %d (no location)"
         ([%show: Lexer.token] found)
         offset)
;;

let parse_channel filename ch =
  Reporter.tracef "when parsing file `%s`" filename
  @@ fun () ->
  let lexbuf = Lexing.from_channel ch in
  lexbuf.Lexing.lex_curr_p
  <- { lexbuf.Lexing.lex_curr_p with Lexing.pos_fname = filename };
  let toks = Array.of_list (tokens filename lexbuf) in
  parse_buf ~name:filename toks
;;

let parse_file filename =
  let ch = open_in filename in
  Fun.protect ~finally:(fun _ -> close_in ch) @@ fun _ -> parse_channel filename ch
;;

let parse_expression_string ~source (src : string) : Surface.preterm =
  let lexbuf = Lexing.from_string src in
  lexbuf.Lexing.lex_curr_p <- { lexbuf.Lexing.lex_curr_p with Lexing.pos_fname = source };
  let toks = Array.of_list (tokens source lexbuf) in
  match P.parse Grammar.p_term toks 0 with
  | next, t when next = Array.length toks - 1 -> t
  | next, _ ->
    let lt = toks.(next) in
    Reporter.fatalf
      ?loc:lt.Asai.Range.loc
      Parse_error
      "unexpected trailing token `%s` after expression"
      ([%show: Lexer.token] lt.Asai.Range.value)
  | exception P.ParseFailure { offset; loc; found } ->
    (match loc with
     | Some loc ->
       Reporter.fatalf
         ~loc
         Parse_error
         "unexpected token `%s` at offset %d"
         ([%show: Lexer.token] found)
         offset
     | None ->
       Reporter.fatalf
         Parse_error
         "unexpected token `%s` at offset %d (no location)"
         ([%show: Lexer.token] found)
         offset)
;;

(* Lex a source string to a list of tokens (location-stripped, EOF dropped) for
   inline tests of the lexer. *)
let lex_to_list src =
  let lexbuf = Lexing.from_string src in
  let rec loop acc =
    match Lexer.token lexbuf with
    | Lexer.EOF -> List.rev acc
    | t -> loop (t :: acc)
  in
  loop []
;;

let%expect_test "lex symbol: +" =
  print_string @@ [%show: Lexer.token list] (lex_to_list "+");
  [%expect {| [<symbol:+>] |}]
;;

let%expect_test "lex symbol: <*>" =
  print_string @@ [%show: Lexer.token list] (lex_to_list "<*>");
  [%expect {| [<symbol:<*>>] |}]
;;

let%expect_test "lex symbol vs reserved: -> stays ARROW" =
  print_string @@ [%show: Lexer.token list] (lex_to_list "->");
  [%expect {| [->] |}]
;;

let%expect_test "lex symbol vs reserved: <= stays STACK_ARROW" =
  print_string @@ [%show: Lexer.token list] (lex_to_list "<=");
  [%expect {| [<=] |}]
;;

let%expect_test "lex symbol: longest-match beats reserved (-->>)" =
  (* ->> contains -> as prefix; longest-match makes the whole run a SYMBOL. *)
  print_string @@ [%show: Lexer.token list] (lex_to_list "->>");
  [%expect {| [<symbol:->>>] |}]
;;

let%expect_test "lex symbol: comma is a SYMBOL char" =
  print_string @@ [%show: Lexer.token list] (lex_to_list ",");
  [%expect {| [<symbol:,>] |}]
;;

let%expect_test "lex symbols mixed with idents" =
  print_string @@ [%show: Lexer.token list] (lex_to_list "x + y");
  [%expect {| [<identifier:x>; <symbol:+>; <identifier:y>] |}]
;;

let%expect_test "lex bare underscore as identifier" =
  print_string @@ [%show: Lexer.token list] (lex_to_list "_");
  [%expect {| [<identifier:_>] |}]
;;

let%expect_test "lex underscore in lambda position" =
  print_string @@ [%show: Lexer.token list] (lex_to_list "\\_ => x");
  [%expect {| [\; <identifier:_>; =>; <identifier:x>] |}]
;;

let%expect_test "lex string: simple" =
  print_string @@ [%show: Lexer.token list] (lex_to_list "\"hello\"");
  [%expect {| [<string:hello>] |}]
;;

let%expect_test "lex string: template" =
  print_string @@ [%show: Lexer.token list] (lex_to_list "\"\\x + \\y\"");
  [%expect {| [<string:\x + \y>] |}]
;;

let%expect_test "lex operator keyword" =
  print_string @@ [%show: Lexer.token list] (lex_to_list "\\operator");
  [%expect {| [\operator] |}]
;;

let%expect_test "lex full operator decl" =
  print_string
  @@ [%show: Lexer.token list]
       (lex_to_list "\\operator \"\\x + \\y\" => add \\weaker_than: *");
  [%expect
    {|
    [\operator; <string:\x + \y>; =>; <identifier:add>; \weaker_than; :;
      <symbol:*>]
    |}]
;;

(* Parse a complete source string into its top-level forms (location-stripped
   for compact display in expect-test output). *)
let parse_module_for_test src =
  Reporter.run ~emit:(fun _ -> ()) ~fatal:(fun _ -> exit 1)
  @@ fun () ->
  let lexbuf = Lexing.from_string src in
  let toks = Array.of_list (tokens "<parser-test>" lexbuf) in
  parse_buf ~name:"<parser-test>" toks
;;

let parse_tops_for_test src =
  Reporter.run ~emit:(fun _ -> ()) ~fatal:(fun _ -> exit 1)
  @@ fun () ->
  let lexbuf = Lexing.from_string src in
  let toks = Array.of_list (tokens "<parser-test>" lexbuf) in
  let m = parse_buf ~name:"<parser-test>" toks in
  List.map (fun lt -> lt.Asai.Range.value) m.Surface.tops
;;

let%expect_test "parse: single \\export line, no decls" =
  let m = parse_module_for_test "\\export foo bar\n" in
  Printf.printf
    "exports=[%s] tops=%d"
    (String.concat ";" m.Surface.exports)
    (List.length m.Surface.tops);
  [%expect {| exports=[foo;bar] tops=0 |}]
;;

let%expect_test "parse: bare operator decl, no options" =
  print_string
  @@ [%show: Surface.top list] (parse_tops_for_test "\\operator \"\\x + \\y\" => add\n");
  [%expect
    {|
    [Surface.Operator_decl {template = "\\x + \\y"; body = <soup:[N(add)]>;
       options = []}
      ]
    |}]
;;

let%expect_test "parse: operator with \\stronger_than" =
  print_string
  @@ [%show: Surface.top list]
       (parse_tops_for_test "\\operator \"\\x * \\y\" => mul\n  \\stronger_than: +\n");
  [%expect
    {|
    [Surface.Operator_decl {template = "\\x * \\y"; body = <soup:[N(mul)]>;
       options = [(Surface.OO_Stronger_than [["+"]])]}
      ]
    |}]
;;

let%expect_test "parse: operator with \\associativity" =
  print_string
  @@ [%show: Surface.top list]
       (parse_tops_for_test
          "\\operator \"\\x + \\y\" => add\n  \\associativity: \\left\n");
  [%expect
    {|
    [Surface.Operator_decl {template = "\\x + \\y"; body = <soup:[N(add)]>;
       options = [(Surface.OO_Associativity Surface.OA_Left)]}
      ]
    |}]
;;

let%expect_test "parse: operator mixfix with multi-part name in option" =
  print_string
  @@ [%show: Surface.top list]
       (parse_tops_for_test
          "\\operator \"if \\x then \\y else \\z\" => ite\n  \\weaker_than: +\n");
  [%expect
    {|
    [Surface.Operator_decl {template = "if \\x then \\y else \\z";
       body = <soup:[N(ite)]>; options = [(Surface.OO_Weaker_than [["+"]])]}
      ]
    |}]
;;

let%expect_test "parse: operator decl alongside let" =
  print_string
  @@ [%show: Surface.top list]
       (parse_tops_for_test
          "\\operator \"\\x + \\y\" => add\n\\let two : Nat => add zero zero\n");
  [%expect
    {|
    [Surface.Operator_decl {template = "\\x + \\y"; body = <soup:[N(add)]>;
       options = []};
      (Surface.Let ("two", [], <soup:[N(Nat)]>, <soup:[N(add); N(zero); N(zero)]>
         ))
      ]
    |}]
;;

let%expect_test "reject: legacy := syntax" =
  let lexbuf = Lexing.from_string "\\let foo : U := bar\n" in
  let toks = Array.of_list (tokens "<reject-legacy>" lexbuf) in
  (try
     let _ = parse_buf ~name:"<reject-legacy>" toks in
     print_endline "UNEXPECTED: legacy := parsed successfully"
   with
   | _ -> print_endline "rejected as expected");
  [%expect {| rejected as expected |}]
;;

let%expect_test "lex export keyword" =
  print_string @@ [%show: Lexer.token list] (lex_to_list "\\export foo bar");
  [%expect {| [\export; <identifier:foo>; <identifier:bar>] |}]
;;

let%expect_test "lex \\record keyword" =
  print_string @@ [%show: Lexer.token list] (lex_to_list "\\record");
  [%expect {| [\record] |}]
;;

let%expect_test "lex dot punctuation" =
  print_string @@ [%show: Lexer.token list] (lex_to_list ".");
  [%expect {| [.] |}]
;;

let%expect_test "lex dot in field projection context" =
  print_string @@ [%show: Lexer.token list] (lex_to_list "r.field");
  [%expect {| [<identifier:r>; .; <identifier:field>] |}]
;;

let%expect_test "parse: multiple \\export lines concatenated in source order" =
  let m = parse_module_for_test "\\export foo\n\\export bar baz\n" in
  Printf.printf "exports=[%s]" (String.concat ";" m.Surface.exports);
  [%expect {| exports=[foo;bar;baz] |}]
;;

let%expect_test "parse: imports then exports then tops" =
  let m = parse_module_for_test "\\import nat\n\\export id\n\\let id : U => U\n" in
  Printf.printf
    "imports=%d exports=[%s] tops=%d"
    (List.length m.Surface.imports)
    (String.concat ";" m.Surface.exports)
    (List.length m.Surface.tops);
  [%expect {| imports=1 exports=[id] tops=1 |}]
;;

let%expect_test "reject: \\export after a top is a parse error" =
  let lexbuf = Lexing.from_string "\\let x : U => U\n\\export x\n" in
  let toks = Array.of_list (tokens "<reject-late-export>" lexbuf) in
  (try
     let _ = parse_buf ~name:"<reject-late-export>" toks in
     print_endline "UNEXPECTED: late \\export parsed successfully"
   with
   | _ -> print_endline "rejected as expected");
  [%expect {| rejected as expected |}]
;;

let%expect_test "reject: qualified path in \\export" =
  let lexbuf = Lexing.from_string "\\export Nat/zero\n" in
  let toks = Array.of_list (tokens "<reject-qual>" lexbuf) in
  (try
     let _ = parse_buf ~name:"<reject-qual>" toks in
     print_endline "UNEXPECTED: qualified export parsed"
   with
   | _ -> print_endline "rejected as expected");
  [%expect {| rejected as expected |}]
;;

let%expect_test "reject: duplicate name within one \\export line" =
  let lexbuf = Lexing.from_string "\\export foo foo\n" in
  let toks = Array.of_list (tokens "<reject-dup-line>" lexbuf) in
  (try
     let _ = parse_buf ~name:"<reject-dup-line>" toks in
     print_endline "UNEXPECTED: duplicate parsed"
   with
   | _ -> print_endline "rejected as expected");
  [%expect {| rejected as expected |}]
;;

let%expect_test "reject: duplicate name across two \\export lines" =
  let lexbuf = Lexing.from_string "\\export foo\n\\export foo\n" in
  let toks = Array.of_list (tokens "<reject-dup-cross>" lexbuf) in
  (try
     let _ = parse_buf ~name:"<reject-dup-cross>" toks in
     print_endline "UNEXPECTED: cross-line duplicate parsed"
   with
   | _ -> print_endline "rejected as expected");
  [%expect {| rejected as expected |}]
;;
