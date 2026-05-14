(* Typed-algebraic parser combinators (Krishnaswami-style).
   Strictly LL(1) at the combinator level, with two small
   hand-coded disambiguators that peek the token buffer:

     1. `(` ... : in atom position, peek for `IDENT+ :` -> binder; else paren term.
     2. `\` ... : in atom position, peek for `(` or `{` -> typed lambda; else
        untyped lambda with bare identifiers.

   Everything else type-checks under the typed-algebraic discipline, so the
   grammar is statically proven unambiguous along those paths. *)

module C : sig
  type tag =
    | T_DATA
    | T_LET
    | T_IMPORT
    | T_UNIVERSE
    | T_ASSIGN
    | T_ARROW
    | T_COLON
    | T_LAMBDA
    | T_DOT
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
    | T_ASSIGN
    | T_ARROW
    | T_COLON
    | T_LAMBDA
    | T_DOT
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

  let tag_index = function
    | T_DATA -> 0
    | T_LET -> 1
    | T_IMPORT -> 2
    | T_UNIVERSE -> 3
    | T_ASSIGN -> 4
    | T_ARROW -> 5
    | T_COLON -> 6
    | T_LAMBDA -> 7
    | T_DOT -> 8
    | T_VERT -> 9
    | T_JOIN -> 10
    | T_LPAREN -> 11
    | T_RPAREN -> 12
    | T_LBRACKET -> 13
    | T_RBRACKET -> 14
    | T_IDENT -> 15
    | T_EOF -> 16
    | T_WHERE -> 17
    | T_STACK_ARROW -> 18
    | T_FAT_ARROW -> 19
    | T_QMARK -> 20
  ;;

  let tag_of : Lexer.token -> tag = function
    | Lexer.DATA -> T_DATA
    | Lexer.LET -> T_LET
    | Lexer.IMPORT -> T_IMPORT
    | Lexer.UNIVERSE -> T_UNIVERSE
    | Lexer.ASSIGN -> T_ASSIGN
    | Lexer.ARROW -> T_ARROW
    | Lexer.COLON -> T_COLON
    | Lexer.LAMBDA -> T_LAMBDA
    | Lexer.DOT -> T_DOT
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
  ;;

  type t = int

  let empty = 0
  let top = 0x1FFFFF
  let one t = 1 lsl tag_index t
  let of_list ts = List.fold_left (fun s t -> s lor (1 lsl tag_index t)) 0 ts
  let union = ( lor )
  let inter = ( land )
  let negate s = lnot s land 0x1FFFFF
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
            (try
               let bpos, _ = Asai.Range.split lstart in
               let _, epos = Asai.Range.split lend in
               Some (Asai.Range.make (bpos, epos))
             with
             | Invalid_argument _ -> Some lstart)
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

  let p_path : string list t =
    let+ first = ident
    and+ rest =
      star
        (let+ _ = tok C.T_DOT
         and+ x = ident in
         x)
    in
    first :: rest
  ;;

  let p_import : string list t =
    let+ _ = tok C.T_IMPORT
    and+ path = p_path in
    path
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
        List.map (fun name -> { Syntax.name; bound; implicit }) names
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
        let+ loc, name = ident_loc in
        wrap_loc loc (S.Var name)
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
              (try
                 let _, q_end = Asai.Range.split q in
                 let j_start, _ = Asai.Range.split j in
                 q_end.offset = j_start.offset
               with
               | Invalid_argument _ -> false)
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
                  (try
                     let bpos, _ = Asai.Range.split q in
                     let _, epos = Asai.Range.split j in
                     Some (Asai.Range.make (bpos, epos))
                   with
                   | Invalid_argument _ -> qmark_loc)
                | Some _, None -> qmark_loc
                | None, _ -> ident_loc
              in
              after + 1, wrap_loc span (S.Goal (Some s))
            | _ -> assert false)
          else after, wrap_loc qmark_loc (S.Goal None)
        in
        { tp; parse }
      in
      (* atom_no_bracket is used in the "explicit" branch of `arg` so the alt
         with `{ atom }` doesn't double-claim LBRACKET. *)
      let atom_no_bracket : S.preterm t =
        ident_atom || goal_atom || p_atom_lparen || p_atom_lambda
      in
      let atom : S.preterm t = atom_no_bracket || p_atom_lbracket in
      let arg : (bool * S.preterm) t =
        (let+ _ = tok C.T_LBRACKET
         and+ a = atom
         and+ _ = tok C.T_RBRACKET in
         true, a)
        ||
        let+ a = atom_no_bracket in
        false, a
      in
      let spine : S.preterm t =
        let+ head = atom
        and+ args = star arg in
        List.fold_left (fun acc (impl, x) -> S.App (impl, acc, x)) head args
      in
      (* max_level: spine ('⊔' spine)*, right-associative to match legacy *)
      let max_level : S.preterm t =
        let+ head = spine
        and+ tail =
          star
            (let+ _ = tok C.T_JOIN
             and+ s = spine in
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
      | Some r -> S.Pi ({ name = "_"; bound = lhs; implicit = false }, r))
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
    List.map (fun name -> { Syntax.name; bound = ty; implicit = false }) names
  ;;

  let p_binding_brackets : S.preterm Syntax.binder list t =
    let+ _ = tok C.T_LBRACKET
    and+ names = p_idents
    and+ _ = tok C.T_COLON
    and+ ty = p_term
    and+ _ = tok C.T_RBRACKET in
    List.map (fun name -> { Syntax.name; bound = ty; implicit = true }) names
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
    { Syntax.name; bound = ty; implicit = false }
  ;;

  let p_stack_move : S.stack_move t =
    let+ _ = tok C.T_STACK_ARROW
    and+ name = ident in
    match name with
    | "intro" -> S.Intro
    | "split" -> S.Split
    | other ->
      Reporter.fatalf Parse_error "expected `intro` or `split` after `<=`, got `%s`" other
  ;;

  let p_pattern : S.pattern t =
    (let+ name = ident in
     S.PVar name)
    ||
    let+ _ = tok C.T_LPAREN
    and+ ctor = ident
    and+ vs = star ident
    and+ _ = tok C.T_RPAREN in
    S.PCon (ctor, vs)
  ;;

  let p_clause : S.clause t =
    let+ _ = tok C.T_VERT
    and+ head = ident
    and+ patterns = star p_pattern
    and+ _ = tok C.T_FAT_ARROW
    and+ body = p_term in
    { S.head; patterns; body }
  ;;

  type elim_header_data =
    { head : string
    ; intros : string list
    ; target : string
    }

  let p_elim_header : elim_header_data t =
    let+ head = ident
    and+ intros = star ident
    and+ _ = tok C.T_STACK_ARROW
    and+ elim_kw = ident
    and+ target = ident in
    match elim_kw with
    | "elim" -> { head; intros; target }
    | other ->
      Reporter.fatalf
        Parse_error
        "expected `elim` after intros in `where`-line, got `%s`"
        other
  ;;

  type where_head =
    | WH_Elim of elim_header_data
    | WH_Moves of S.stack_move list

  type let_body =
    | LB_Assign of S.preterm
    | LB_Where of S.stack_move list * S.clause list
    | LB_Elim of elim_header_data * S.clause list

  let p_let_body : let_body t =
    (let+ _ = tok C.T_ASSIGN
     and+ tm = p_term in
     LB_Assign tm)
    ||
    let+ _ = tok C.T_WHERE
    and+ wh =
      (let+ hdr = p_elim_header in
       WH_Elim hdr)
      ||
      let+ moves = star p_stack_move in
      WH_Moves moves
    and+ clauses = star p_clause in
    match wh with
    | WH_Elim hdr -> LB_Elim (hdr, clauses)
    | WH_Moves moves -> LB_Where (moves, clauses)
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
    | LB_Elim ({ head; intros; target }, clauses) ->
      if not (String.equal head name)
      then
        Reporter.fatalf
          Parse_error
          "elim-header head `%s` must match let name `%s`"
          head
          name;
      { Asai.Range.loc
      ; value =
          S.Elim_def { name; params = bindings; signature = ty; intros; target; clauses }
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

  let p_top : S.top Asai.Range.located t = p_let_top || p_data_top || p_universe_top

  let p_tops_loop : S.top Asai.Range.located list t =
    fix (fun self ->
      (let+ t = p_top
       and+ rest = self in
       t :: rest)
      || let+ _ = tok C.T_EOF in
         [])
  ;;

  let p_module_named (name : string) : S.t t =
    fix (fun self ->
      (let+ i = p_import
       and+ rest = self in
       { rest with S.imports = i :: rest.S.imports })
      || let+ tops = p_tops_loop in
         { S.name; imports = []; tops })
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
  | _, m -> m
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
