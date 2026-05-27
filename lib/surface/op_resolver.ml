(* Operator resolver.

   The parser emits flat `Op_soup` nodes for every expression position. This
   module is responsible for rewriting each `Op_soup` back into a normal
   App / Var spine using the in-scope operator table.

   The pipeline is:

     parser  →  Surface.t with Op_soup nodes  →  Op_resolver  →  Surface.t with
                                                                  no Op_soup
              →  Elaborator  →  Kernel

   This file consists of:
     1. Template language: parsing, validation, shape derivation
     2. Op_table: collection of declarations with duplicate detection
     3. Precedence graph and topo sort
     4. Danielsson-Norell parser over the soup
     5. Surface-tree rewrite that drives all of the above. *)

(* ===========================================================================
   1. Template language
   ===========================================================================
   Templates come in as raw strings from the parser. We split on whitespace
   into "parts"; each part is either a hole (`\name`) or a literal token
   that must lex (via the main lexer) as exactly one IDENT or SYMBOL.
   Literal parts may not start with `\`, which is reserved for hole markers
   and language keywords. *)

type name_part =
  | Hole of string
  | Lit of string
[@@deriving show]

type op_shape =
  | Closed
  | Prefix
  | Postfix
  | Infix
[@@deriving show]

(* Split a template string on whitespace into raw chunks. Empty leading /
   trailing whitespace is dropped. *)
let split_parts (s : string) : string list =
  let n = String.length s in
  let buf = Buffer.create 16 in
  let acc = ref [] in
  let flush () =
    if Buffer.length buf > 0
    then begin
      acc := Buffer.contents buf :: !acc;
      Buffer.clear buf
    end
  in
  for i = 0 to n - 1 do
    match s.[i] with
    | ' ' | '\t' | '\n' | '\r' -> flush ()
    | c -> Buffer.add_char buf c
  done;
  flush ();
  List.rev !acc
;;

(* Re-lex one chunk via the main Lexer. Returns the chunk's token-kind tag
   (or fails as `None` on any unexpected lex outcome). Used to validate
   literal parts. *)
let classify_chunk (s : string) : [ `Ident | `Symbol | `Bad ] =
  match
    let lexbuf = Lexing.from_string s in
    let t1 =
      try Some (Lexer.token lexbuf) with
      | Lexer.SyntaxError _ -> None
    in
    let t2 =
      try Some (Lexer.token lexbuf) with
      | Lexer.SyntaxError _ -> None
    in
    t1, t2
  with
  | Some (Lexer.IDENT _), Some Lexer.EOF -> `Ident
  | Some (Lexer.SYMBOL _), Some Lexer.EOF -> `Symbol
  | _ -> `Bad
;;

(* Parse one chunk into a name_part. Holes look like "\name" and the name
   itself must be a valid identifier. Literal parts must classify as IDENT
   or SYMBOL on re-lexing — they may not start with `\`, which is reserved
   for hole markers and language keywords. *)
let parse_chunk ~template (chunk : string) : name_part =
  let n = String.length chunk in
  if n >= 1 && chunk.[0] = '\\'
  then begin
    let name = String.sub chunk 1 (n - 1) in
    if String.length name = 0
    then
      Reporter.fatalf
        Parse_error
        "invalid operator template `%s`: bare `\\` is not a valid hole name"
        template;
    (* Hole name must lex as a single IDENT. *)
    (match classify_chunk name with
     | `Ident -> ()
     | _ ->
       Reporter.fatalf
         Parse_error
         "invalid operator template `%s`: hole name `\\%s` is not a valid identifier"
         template
         name);
    Hole name
  end
  else
    begin match classify_chunk chunk with
    | `Ident | `Symbol -> Lit chunk
    | `Bad ->
      Reporter.fatalf
        Parse_error
        "invalid operator template `%s`: part `%s` must be a single identifier or symbol \
         (no reserved punctuation, no spaces, no quotes; `\\` is reserved for hole names \
         and may not begin a literal part)"
        template
        chunk
    end
;;

(* Derive shape from a non-empty parts list. *)
let derive_shape (parts : name_part list) : op_shape =
  let first = List.hd parts in
  let last = List.hd (List.rev parts) in
  match first, last with
  | Lit _, Lit _ -> Closed
  | Lit _, Hole _ -> Prefix
  | Hole _, Lit _ -> Postfix
  | Hole _, Hole _ -> Infix
;;

(* Walk a parts list checking the no-adjacent-holes invariant. *)
let check_no_adjacent_holes ~template (parts : name_part list) : unit =
  let rec walk = function
    | Hole h1 :: Hole h2 :: _ ->
      Reporter.fatalf
        Parse_error
        "invalid operator template `%s`: holes `\\%s` and `\\%s` are adjacent (need a \
         literal part between them)"
        template
        h1
        h2
    | _ :: rest -> walk rest
    | [] -> ()
  in
  walk parts
;;

(* Walk a parts list checking that hole names are pairwise distinct. *)
let check_distinct_hole_names ~template (parts : name_part list) : unit =
  let rec walk seen = function
    | [] -> ()
    | Hole h :: _ when List.exists (String.equal h) seen ->
      Reporter.fatalf
        Parse_error
        "invalid operator template `%s`: hole name `\\%s` appears more than once"
        template
        h
    | Hole h :: rest -> walk (h :: seen) rest
    | Lit _ :: rest -> walk seen rest
  in
  walk [] parts
;;

(* Parse + validate a template string into a parts list. Raises on any
   problem with a precise message. *)
let parse_template (template : string) : name_part list =
  let chunks = split_parts template in
  (match chunks with
   | [] ->
     Reporter.fatalf
       Parse_error
       "invalid operator template `%s`: template must contain at least one part"
       template
   | _ -> ());
  let parts = List.map (parse_chunk ~template) chunks in
  let has_hole =
    List.exists
      (function
        | Hole _ -> true
        | _ -> false)
      parts
  in
  let has_lit =
    List.exists
      (function
        | Lit _ -> true
        | _ -> false)
      parts
  in
  if not has_hole
  then
    Reporter.fatalf
      Parse_error
      "invalid operator template `%s`: template must contain at least one hole (`\\name`)"
      template;
  if not has_lit
  then
    Reporter.fatalf
      Parse_error
      "invalid operator template `%s`: template must contain at least one literal part"
      template;
  check_no_adjacent_holes ~template parts;
  check_distinct_hole_names ~template parts;
  parts
;;

(* The literal parts of a template, in order, used as the cross-reference
   name path for `\weaker_than:` / `\stronger_than:` / `\same_as:`. *)
let ref_path_of_parts (parts : name_part list) : string list =
  List.filter_map
    (function
      | Lit s -> Some s
      | Hole _ -> None)
    parts
;;

(* The hole names of a template, in template order. Used to scope holes
   into the body and to position match-results during lowering. *)
let hole_names_of_parts (parts : name_part list) : string list =
  List.filter_map
    (function
      | Hole s -> Some s
      | Lit _ -> None)
    parts
;;

(* ===========================================================================
   2. Operator declarations and table
   ===========================================================================
   An `op_decl` is a fully-validated, table-ready operator: template,
   derived shape, associativity, body, and the raw precedence constraints. *)

type op_constraint =
  | C_Weaker_than of string list
  | C_Stronger_than of string list
  | C_Same_as of string list
[@@deriving show]

type op_decl =
  { template : name_part list
  ; shape : op_shape
  ; assoc : Surface.op_assoc
  ; body : Surface.preterm
  ; hole_names : string list
  ; ref_path : string list
  ; constraints : op_constraint list
  ; raw_template : string (* original string, for diagnostics *)
  ; origin : string
    (* module name that declared this op; "" when unknown. Used to
       deduplicate the same op arriving via multiple import paths
       (diamond imports) while still rejecting genuine conflicts. *)
  }
[@@deriving show]

type op_table = { decls : op_decl list (* in declaration order *) }

let empty_table : op_table = { decls = [] }

(* Build an op_decl from a Surface.Operator_decl payload. Validates the
   template, associativity, and assembles the constraint list. *)
let make_op_decl
      ~(template : string)
      ~(body : Surface.preterm)
      ~(options : Surface.op_option list)
  : op_decl
  =
  let parts = parse_template template in
  let shape = derive_shape parts in
  let assoc_opt = ref None in
  let constraints = ref [] in
  List.iter
    (fun opt ->
       match opt with
       | Surface.OO_Weaker_than paths ->
         List.iter (fun p -> constraints := C_Weaker_than p :: !constraints) paths
       | Surface.OO_Stronger_than paths ->
         List.iter (fun p -> constraints := C_Stronger_than p :: !constraints) paths
       | Surface.OO_Same_as paths ->
         List.iter (fun p -> constraints := C_Same_as p :: !constraints) paths
       | Surface.OO_Associativity a ->
         (match !assoc_opt with
          | Some _ ->
            Reporter.fatalf
              Parse_error
              "operator `%s` has more than one `\\associativity:` option"
              template
          | None -> assoc_opt := Some a))
    options;
  (* \associativity is only meaningful for binary infix operators (exactly
     2 holes, Infix shape). *)
  let n_holes = List.length (hole_names_of_parts parts) in
  (match !assoc_opt with
   | Some _ when shape <> Infix || n_holes <> 2 ->
     Reporter.fatalf
       Parse_error
       "operator `%s` is not binary infix; `\\associativity:` is not allowed here"
       template
   | _ -> ());
  let assoc = Option.value !assoc_opt ~default:Surface.OA_None in
  { template = parts
  ; shape
  ; assoc
  ; body
  ; hole_names = hole_names_of_parts parts
  ; ref_path = ref_path_of_parts parts
  ; constraints = List.rev !constraints
  ; raw_template = template
  ; origin = ""
  }
;;

(* Add a decl to a table; duplicate templates error. Used for ops being
   declared within a single module. *)
let add_decl (decl : op_decl) (table : op_table) : op_table =
  let dup = List.exists (fun d -> d.template = decl.template) table.decls in
  if dup
  then Reporter.fatalf Parse_error "duplicate operator template `%s`" decl.raw_template;
  { decls = decl :: table.decls }
;;

(* Merge a decl imported from another module. If the same operator (same
   template AND same origin module) is already present, this is a diamond
   import — silently dedupe. A clashing template from a different origin
   is a genuine conflict and errors. *)
let merge_decl (decl : op_decl) (table : op_table) : op_table =
  match List.find_opt (fun d -> d.template = decl.template) table.decls with
  | Some existing when existing.origin <> "" && existing.origin = decl.origin -> table
  | Some _ ->
    Reporter.fatalf Parse_error "duplicate operator template `%s`" decl.raw_template
  | None -> { decls = decl :: table.decls }
;;

let%expect_test "parse_template: simple infix" =
  print_string @@ [%show: name_part list] (parse_template "\\x + \\y");
  [%expect {| [(Op_resolver.Hole "x"); (Op_resolver.Lit "+"); (Op_resolver.Hole "y")] |}]
;;

let%expect_test "parse_template: ternary mixfix" =
  print_string @@ [%show: name_part list] (parse_template "if \\x then \\y else \\z");
  [%expect
    {|
    [(Op_resolver.Lit "if"); (Op_resolver.Hole "x"); (Op_resolver.Lit "then");
      (Op_resolver.Hole "y"); (Op_resolver.Lit "else"); (Op_resolver.Hole "z")]
    |}]
;;

let%expect_test "parse_template: postfix" =
  print_string @@ [%show: name_part list] (parse_template "\\x !");
  [%expect {| [(Op_resolver.Hole "x"); (Op_resolver.Lit "!")] |}]
;;

let%expect_test "derive_shape: infix" =
  print_string @@ show_op_shape (derive_shape (parse_template "\\x + \\y"));
  [%expect {| Op_resolver.Infix |}]
;;

let%expect_test "derive_shape: prefix" =
  print_string @@ show_op_shape (derive_shape (parse_template "! \\x"));
  [%expect {| Op_resolver.Prefix |}]
;;

let%expect_test "derive_shape: postfix" =
  print_string @@ show_op_shape (derive_shape (parse_template "\\x !"));
  [%expect {| Op_resolver.Postfix |}]
;;

let%expect_test "derive_shape: closed" =
  print_string @@ show_op_shape (derive_shape (parse_template "begin \\x end"));
  [%expect {| Op_resolver.Closed |}]
;;

let%expect_test "ref_path / hole_names" =
  let parts = parse_template "if \\c then \\t else \\e" in
  Printf.printf
    "ref_path=%s hole_names=%s"
    ([%show: string list] (ref_path_of_parts parts))
    ([%show: string list] (hole_names_of_parts parts));
  [%expect {| ref_path=["if"; "then"; "else"] hole_names=["c"; "t"; "e"] |}]
;;

(* Run a body that fatal-errors and catch the message tag for inline tests. *)
let try_validate (template : string) : string =
  try
    Reporter.run
      ~emit:(fun _ -> ())
      ~fatal:(fun _ -> "rejected")
      (fun () ->
         let _ = parse_template template in
         "ok")
  with
  | _ -> "rejected"
;;

let%expect_test "validate: rejects template with no holes" =
  print_string (try_validate "+");
  [%expect {| rejected |}]
;;

let%expect_test "validate: rejects template with no literal parts" =
  print_string (try_validate "\\x \\y");
  [%expect {| rejected |}]
;;

let%expect_test "validate: rejects adjacent holes" =
  print_string (try_validate "\\x \\y + \\z");
  [%expect {| rejected |}]
;;

let%expect_test "validate: rejects duplicate hole names" =
  print_string (try_validate "\\x + \\x");
  [%expect {| rejected |}]
;;

let%expect_test "validate: rejects reserved punctuation as literal" =
  (* `->` is a reserved token, not IDENT/SYMBOL. *)
  print_string (try_validate "\\x -> \\y");
  [%expect {| rejected |}]
;;

let%expect_test "validate: accepts a normal binary infix" =
  print_string (try_validate "\\x + \\y");
  [%expect {| ok |}]
;;

let%expect_test "validate: bare `\\` is not a valid hole name" =
  print_string (try_validate "\\x \\ \\y");
  [%expect {| rejected |}]
;;

let%expect_test "add_decl: detects duplicate template" =
  let mk t = make_op_decl ~template:t ~body:(Surface.Var [ "f" ]) ~options:[] in
  let outcome =
    Reporter.run
      ~emit:(fun _ -> ())
      ~fatal:(fun _ -> "rejected")
      (fun () ->
         let t = empty_table in
         let t = add_decl (mk "\\x + \\y") t in
         let _ = add_decl (mk "\\x + \\y") t in
         "ok")
  in
  print_string outcome;
  [%expect {| rejected |}]
;;

let%expect_test "make_op_decl: \\associativity on non-infix is rejected" =
  let outcome =
    Reporter.run
      ~emit:(fun _ -> ())
      ~fatal:(fun _ -> "rejected")
      (fun () ->
         let _ =
           make_op_decl
             ~template:"if \\x then \\y else \\z"
             ~body:(Surface.Var [ "ite" ])
             ~options:[ Surface.OO_Associativity Surface.OA_Left ]
         in
         "ok")
  in
  print_string outcome;
  [%expect {| rejected |}]
;;

(* ===========================================================================
   3. Precedence graph + topo sort
   ===========================================================================
   Each op_decl carries a list of `op_constraint`s naming OTHER operators by
   their ref_path. From those we build a directed graph where an edge
   `u → v` means "u parses TIGHTER than v" (u is at a lower precedence
   level number). `\same_as:` merges nodes into equivalence classes via
   union-find. Cycles between non-equivalent classes are errors. *)

module Path_map = Map.Make (struct
    type t = string list

    let compare = compare
  end)

module Path_set = Set.Make (struct
    type t = string list

    let compare = compare
  end)

(* Union-find over ref_paths. *)
module UF = struct
  type t = { mutable parent : string list Path_map.t }

  let create () : t = { parent = Path_map.empty }

  let rec find (uf : t) (x : string list) : string list =
    match Path_map.find_opt x uf.parent with
    | None ->
      uf.parent <- Path_map.add x x uf.parent;
      x
    | Some p when p = x -> x
    | Some p ->
      let r = find uf p in
      uf.parent <- Path_map.add x r uf.parent;
      r
  ;;

  let union (uf : t) (a : string list) (b : string list) : unit =
    let ra = find uf a in
    let rb = find uf b in
    if ra <> rb then uf.parent <- Path_map.add ra rb uf.parent
  ;;
end

type prec_graph =
  { uf : UF.t (* equivalence classes *)
  ; mutable edges : Path_set.t Path_map.t
    (* edges.(u) = set of v such that u → v (u tighter than v).
                                  Keys / values are CLASS REPRESENTATIVES. *)
  ; mutable known_paths : Path_set.t
    (* every ref_path that ever appeared, including those only referenced. *)
  }

let make_graph () : prec_graph =
  { uf = UF.create (); edges = Path_map.empty; known_paths = Path_set.empty }
;;

let add_node (g : prec_graph) (p : string list) : unit =
  let _ = UF.find g.uf p in
  g.known_paths <- Path_set.add p g.known_paths
;;

(* Add a tighter → looser edge between class representatives. *)
let add_edge (g : prec_graph) ~(tighter : string list) ~(looser : string list) : unit =
  add_node g tighter;
  add_node g looser;
  let t = UF.find g.uf tighter in
  let l = UF.find g.uf looser in
  let cur = Option.value (Path_map.find_opt t g.edges) ~default:Path_set.empty in
  g.edges <- Path_map.add t (Path_set.add l cur) g.edges
;;

let unite (g : prec_graph) (a : string list) (b : string list) : unit =
  add_node g a;
  add_node g b;
  UF.union g.uf a b
;;

(* Build the graph from a finalized table. *)
let build_graph (table : op_table) : prec_graph =
  let g = make_graph () in
  (* First pass: register every operator's ref_path as a node. *)
  List.iter (fun d -> add_node g d.ref_path) table.decls;
  (* Second pass: process \same_as first so subsequent edges land on the
     right class representatives. *)
  List.iter
    (fun d ->
       List.iter
         (function
           | C_Same_as p -> unite g d.ref_path p
           | _ -> ())
         d.constraints)
    table.decls;
  (* Third pass: weaker / stronger become directed edges. *)
  List.iter
    (fun d ->
       List.iter
         (function
           | C_Weaker_than p -> add_edge g ~tighter:p ~looser:d.ref_path
           | C_Stronger_than p -> add_edge g ~tighter:d.ref_path ~looser:p
           | C_Same_as _ -> ())
         d.constraints)
    table.decls;
  g
;;

(* Detect a directed cycle. Returns Some (path) on the first cycle found,
   None if acyclic. Walks class representatives only. *)
let detect_cycle (g : prec_graph) : string list list option =
  let on_stack = Hashtbl.create 16 in
  let visited = Hashtbl.create 16 in
  let result = ref None in
  let rec dfs (path : string list list) (n : string list) =
    if !result <> None
    then ()
    else if Hashtbl.mem on_stack n
    then begin
      (* found a cycle — slice the path from n onwards *)
      let rec slice acc = function
        | [] -> List.rev acc
        | x :: _ when x = n -> List.rev (x :: acc)
        | x :: rest -> slice (x :: acc) rest
      in
      result := Some (slice [] (n :: path))
    end
    else if not (Hashtbl.mem visited n)
    then begin
      Hashtbl.add visited n ();
      Hashtbl.add on_stack n ();
      let succ = Option.value (Path_map.find_opt n g.edges) ~default:Path_set.empty in
      Path_set.iter (fun m -> dfs (n :: path) m) succ;
      Hashtbl.remove on_stack n
    end
  in
  let reps =
    Path_set.fold
      (fun p acc ->
         let r = UF.find g.uf p in
         if List.mem r acc then acc else r :: acc)
      g.known_paths
      []
  in
  List.iter (fun n -> dfs [] n) reps;
  !result
;;

(* Compute precedence levels from a finalized table.
   Each level is a list of op_decls that share a precedence class.
   Tighter levels come first. Raises on cycles. *)
type prec_levels = op_decl list list

let compute_levels (table : op_table) : prec_levels =
  let g = build_graph table in
  (match detect_cycle g with
   | Some cycle ->
     let render p = String.concat " " p in
     Reporter.fatalf
       Parse_error
       "precedence cycle detected among operators: %s"
       (String.concat " → " (List.map render cycle))
   | None -> ());
  (* Kahn's algorithm on representatives. *)
  let rep p = UF.find g.uf p in
  let all_reps =
    Path_set.fold (fun p acc -> Path_set.add (rep p) acc) g.known_paths Path_set.empty
  in
  let in_degree = Hashtbl.create 16 in
  Path_set.iter (fun r -> Hashtbl.add in_degree r 0) all_reps;
  Path_map.iter
    (fun _ succ ->
       Path_set.iter
         (fun s ->
            let r = rep s in
            Hashtbl.replace in_degree r (Hashtbl.find in_degree r + 1))
         succ)
    g.edges;
  let level_of_rep = Hashtbl.create 16 in
  let ready =
    Hashtbl.fold (fun r d acc -> if d = 0 then r :: acc else acc) in_degree []
  in
  let queue = ref ready in
  let level = ref 0 in
  while !queue <> [] do
    let here = !queue in
    queue := [];
    List.iter (fun r -> Hashtbl.add level_of_rep r !level) here;
    List.iter
      (fun r ->
         let succ = Option.value (Path_map.find_opt r g.edges) ~default:Path_set.empty in
         Path_set.iter
           (fun s ->
              let rs = rep s in
              let d = Hashtbl.find in_degree rs - 1 in
              Hashtbl.replace in_degree rs d;
              if d = 0 then queue := rs :: !queue)
           succ)
      here;
    incr level
  done;
  (* Bucket decls by their rep's level. *)
  let buckets = Hashtbl.create 16 in
  List.iter
    (fun d ->
       let r = rep d.ref_path in
       let lvl =
         match Hashtbl.find_opt level_of_rep r with
         | Some l -> l
         | None ->
           Reporter.fatalf
             Elab_error
             "internal: operator `%s` did not receive a precedence level"
             d.raw_template
       in
       let cur = Option.value (Hashtbl.find_opt buckets lvl) ~default:[] in
       Hashtbl.replace buckets lvl (d :: cur))
    table.decls;
  let max_level = !level in
  let result = ref [] in
  for lvl = max_level - 1 downto 0 do
    let bucket = Option.value (Hashtbl.find_opt buckets lvl) ~default:[] in
    if bucket <> [] then result := bucket :: !result
  done;
  !result
;;

let%expect_test "compute_levels: two independent operators land in one level" =
  let mk t = make_op_decl ~template:t ~body:(Surface.Var [ "f" ]) ~options:[] in
  let t = empty_table in
  let t = add_decl (mk "\\x + \\y") t in
  let t = add_decl (mk "\\x % \\y") t in
  let levels = compute_levels t in
  Printf.printf
    "%d levels: %s"
    (List.length levels)
    ([%show: string list list]
       (List.map (fun lvl -> List.map (fun d -> d.raw_template) lvl) levels));
  [%expect {| 1 levels: [["\\x + \\y"; "\\x % \\y"]] |}]
;;

let%expect_test "compute_levels: stronger_than gives tighter level" =
  let mk_plus =
    make_op_decl ~template:"\\x + \\y" ~body:(Surface.Var [ "add" ]) ~options:[]
  in
  let mk_times =
    make_op_decl
      ~template:"\\x * \\y"
      ~body:(Surface.Var [ "mul" ])
      ~options:[ Surface.OO_Stronger_than [ [ "+" ] ] ]
  in
  let t = add_decl mk_times (add_decl mk_plus empty_table) in
  let levels = compute_levels t in
  Printf.printf
    "%s"
    ([%show: string list list]
       (List.map (fun lvl -> List.map (fun d -> d.raw_template) lvl) levels));
  [%expect {| [["\\x * \\y"]; ["\\x + \\y"]] |}]
;;

let%expect_test "compute_levels: weaker_than is the inverse" =
  let mk_plus =
    make_op_decl ~template:"\\x + \\y" ~body:(Surface.Var [ "add" ]) ~options:[]
  in
  let mk_or =
    make_op_decl
      ~template:"\\x or \\y"
      ~body:(Surface.Var [ "or_" ])
      ~options:[ Surface.OO_Weaker_than [ [ "+" ] ] ]
  in
  let t = add_decl mk_or (add_decl mk_plus empty_table) in
  let levels = compute_levels t in
  Printf.printf
    "%s"
    ([%show: string list list]
       (List.map (fun lvl -> List.map (fun d -> d.raw_template) lvl) levels));
  [%expect {| [["\\x + \\y"]; ["\\x or \\y"]] |}]
;;

let%expect_test "compute_levels: same_as puts ops in one level" =
  let mk_plus =
    make_op_decl ~template:"\\x + \\y" ~body:(Surface.Var [ "add" ]) ~options:[]
  in
  let mk_minus =
    make_op_decl
      ~template:"\\x - \\y"
      ~body:(Surface.Var [ "sub" ])
      ~options:[ Surface.OO_Same_as [ [ "+" ] ] ]
  in
  let t = add_decl mk_minus (add_decl mk_plus empty_table) in
  let levels = compute_levels t in
  Printf.printf
    "%s"
    ([%show: string list list]
       (List.map (fun lvl -> List.map (fun d -> d.raw_template) lvl) levels));
  [%expect {| [["\\x + \\y"; "\\x - \\y"]] |}]
;;

let%expect_test "compute_levels: detects a cycle" =
  let mk_a =
    make_op_decl
      ~template:"\\x A \\y"
      ~body:(Surface.Var [ "a" ])
      ~options:[ Surface.OO_Stronger_than [ [ "B" ] ] ]
  in
  let mk_b =
    make_op_decl
      ~template:"\\x B \\y"
      ~body:(Surface.Var [ "b" ])
      ~options:[ Surface.OO_Stronger_than [ [ "A" ] ] ]
  in
  let outcome =
    Reporter.run
      ~emit:(fun _ -> ())
      ~fatal:(fun _ -> "rejected")
      (fun () ->
         let t = add_decl mk_b (add_decl mk_a empty_table) in
         let _ = compute_levels t in
         "ok")
  in
  print_string outcome;
  [%expect {| rejected |}]
;;

(* ===========================================================================
   4. Soup parser (Danielsson-Norell-style precedence-graph parse)
   ===========================================================================
   Given a soup-item list and a finalized op_table, produce a Surface.preterm.

   The parser is recursive-descent with backtracking. Levels are ordered
   loosest-first (level 0 is the loosest). For an operator at level L:
   - Inner holes (between two literal parts) parse at level 0 (loosest).
   - Outer slots respect associativity:
       infix \left  : lhs same-level, rhs tighter
       infix \right : lhs tighter,    rhs same-level
       infix \none  : both tighter
       prefix       : rhs same-level (multiple prefix may stack)
       postfix      : lhs same-level (multiple postfix may stack)
   At the tightest "atom" level, juxtaposition of atom-like tokens (atoms
   and free names) becomes application. Implicit-arg attachments
   (`SI_Imp_arg`) attach to the running head as `App (true, ...)`. *)

type tok =
  | TAtom of Surface.preterm
  | TName of string * Asai.Range.t option
  | TImpArg of Surface.preterm

(* The set of strings that appear as a literal part of any operator in the
   table. A name matching one of these is a candidate operator part; a
   name not in this set falls through to a free `Var`. *)
let op_lit_set (table : op_table) : (string, unit) Hashtbl.t =
  let h = Hashtbl.create 16 in
  List.iter
    (fun d ->
       List.iter
         (function
           | Lit s -> Hashtbl.replace h s ()
           | Hole _ -> ())
         d.template)
    table.decls;
  h
;;

type parser_state =
  { toks : tok array
  ; lits : (string, unit) Hashtbl.t
  ; levels : op_decl list array (* loosest first; level 0 = loosest *)
  }

let mk_state (table : op_table) (items : Surface.soup_item list) : parser_state =
  let toks =
    Array.of_list
      (List.map
         (function
           | Surface.SI_Atom p -> TAtom p
           | Surface.SI_Name (s, loc) -> TName (s, loc)
           | Surface.SI_Imp_arg p -> TImpArg p)
         items)
  in
  let levels_tightest_first = compute_levels table in
  let levels_loosest_first = List.rev levels_tightest_first in
  { toks; lits = op_lit_set table; levels = Array.of_list levels_loosest_first }
;;

let is_op_lit (st : parser_state) (s : string) : bool = Hashtbl.mem st.lits s

(* Substitute hole-name occurrences in `body` with the matched subterms.
   Walk body and replace `Var h` with the matched term whenever `h` is one
   of the operator's hole names. If the body mentions no hole, treat it as
   a function and apply it positionally to the holes (bare-ident sugar). *)
let lower_body
      (op : op_decl)
      (matches : Surface.preterm list (* one per hole, in template order *))
  : Surface.preterm
  =
  let hole_set =
    let h = Hashtbl.create 4 in
    List.iter (fun n -> Hashtbl.replace h n ()) op.hole_names;
    h
  in
  let env = List.combine op.hole_names matches in
  let rec sub = function
    | Surface.Located lv -> Surface.Located { lv with value = sub lv.value }
    | Surface.Var [ n ] when Hashtbl.mem hole_set n -> List.assoc n env
    | Surface.Var _ as v -> v
    | Surface.App (impl, f, x) -> Surface.App (impl, sub f, sub x)
    | Surface.Lambda b -> Surface.Lambda { b with bound = sub b.bound }
    | Surface.TypedLambda (b, body) ->
      Surface.TypedLambda ({ b with bound = sub b.bound }, sub body)
    | Surface.Pi (b, body) -> Surface.Pi ({ b with bound = sub b.bound }, sub body)
    | Surface.Max (a, b) -> Surface.Max (sub a, sub b)
    | (Surface.Universe | Surface.Hole | Surface.Goal _) as t -> t
    | Surface.IdAbsurd p -> Surface.IdAbsurd (sub p)
    | Surface.Op_soup _ ->
      Reporter.fatalf
        Elab_error
        "internal: Op_soup inside operator body (resolver should have lowered it)"
    | Surface.RecordLit entries ->
      Surface.RecordLit (List.map (fun (f, e) -> f, sub e) entries)
    | Surface.RecordUpdate (base, entries) ->
      Surface.RecordUpdate (sub base, List.map (fun (f, e) -> f, sub e) entries)
    | Surface.Proj (e, f) -> Surface.Proj (sub e, f)
    | Surface.Inline_elim _ as t -> t
  in
  (* If the body has no hole references, treat it as a function and apply
     it positionally — bare-ident sugar like `=> ite`. *)
  let mentions_holes =
    let r = ref false in
    let rec walk = function
      | Surface.Located lv -> walk lv.value
      | Surface.Var [ n ] when Hashtbl.mem hole_set n -> r := true
      | Surface.Var _ -> ()
      | Surface.App (_, f, x) ->
        walk f;
        walk x
      | Surface.Lambda b -> walk b.bound
      | Surface.TypedLambda (b, body) ->
        walk b.bound;
        walk body
      | Surface.Pi (b, body) ->
        walk b.bound;
        walk body
      | Surface.Max (a, b) ->
        walk a;
        walk b
      | Surface.Universe | Surface.Hole | Surface.Goal _ -> ()
      | Surface.IdAbsurd p -> walk p
      | Surface.Op_soup _ -> ()
      | Surface.RecordLit entries -> List.iter (fun (_, e) -> walk e) entries
      | Surface.RecordUpdate (base, entries) ->
        walk base;
        List.iter (fun (_, e) -> walk e) entries
      | Surface.Proj (e, _) -> walk e
      | Surface.Inline_elim _ -> ()
    in
    walk op.body;
    !r
  in
  if mentions_holes
  then sub op.body
  else
    (* Fold body applied to matches left-to-right, treating the body as the
       function head. *)
    List.fold_left (fun acc m -> Surface.App (false, acc, m)) op.body matches
;;

(* Precedence-climbing parser, extended to mixfix.

   At each level L:
   - First, try Lit-starting ops (Closed / Prefix) — they're not left-
     recursive so we can try them directly.
   - If none match, fall through to parse_level (L+1) (tighter level).
   - With a `base` from one of the above, repeatedly try to extend with
     Hole-starting ops (Postfix / Infix) at this level. Stop looping if
     the extending op forbids chaining (non-associative or right-assoc
     infix, since right-assoc recurses on the rhs). *)

let is_lit_starting (op : op_decl) : bool =
  match op.shape with
  | Closed | Prefix -> true
  | Postfix | Infix -> false
;;

let level_for_outer_rhs (op : op_decl) (lvl : int) : int =
  match op.shape, op.assoc with
  | Prefix, _ -> lvl (* multi-prefix stacking *)
  | Infix, Surface.OA_Right -> lvl
  | Infix, Surface.OA_Left -> lvl + 1
  | Infix, Surface.OA_None -> lvl + 1
  | (Closed | Postfix), _ -> lvl + 1 (* unused *)
;;

(* After we extend with `op` at this level, should we keep looping for
   more extensions at the same level? *)
let extension_chains (op : op_decl) : bool =
  match op.shape, op.assoc with
  | Postfix, _ -> true (* `n ! !` stacks *)
  | Infix, Surface.OA_Left -> true
  | Infix, Surface.OA_Right -> false (* right-recursion in rhs already chains *)
  | Infix, Surface.OA_None -> false
  | (Closed | Prefix), _ -> false (* never extend with these *)
;;

(* Find the index (in template, 0-based) of the LAST Hole. *)
let last_hole_index (template : name_part list) : int =
  let n = List.length template in
  let arr = Array.of_list template in
  let idx = ref (-1) in
  for i = 0 to n - 1 do
    match arr.(i) with
    | Hole _ -> idx := i
    | Lit _ -> ()
  done;
  !idx
;;

let rec parse_level (st : parser_state) (lvl : int) (i : int)
  : (Surface.preterm * int) option
  =
  if lvl >= Array.length st.levels
  then parse_atom_spine st i
  else (
    let ops = st.levels.(lvl) in
    let lit_ops = List.filter is_lit_starting ops in
    let hole_ops = List.filter (fun op -> not (is_lit_starting op)) ops in
    (* Step 1: try Lit-starting ops; else fall through to tighter level. *)
    let initial =
      let rec try_each = function
        | [] -> parse_level st (lvl + 1) i
        | op :: rest ->
          (match try_lit_starting_op st op lvl i with
           | Some r -> Some r
           | None -> try_each rest)
      in
      try_each lit_ops
    in
    match initial with
    | None -> None
    | Some (base, j) -> extend st hole_ops lvl base j)

(* Loop extending `base` with hole-starting ops at this level. *)
and extend
      (st : parser_state)
      (ops : op_decl list)
      (lvl : int)
      (base : Surface.preterm)
      (j : int)
  : (Surface.preterm * int) option
  =
  match try_extend_one st ops lvl base j with
  | None -> Some (base, j)
  | Some (base', j', op) ->
    if extension_chains op then extend st ops lvl base' j' else Some (base', j')

(* Try each hole-starting op until one matches starting from base@j. *)
and try_extend_one
      (st : parser_state)
      (ops : op_decl list)
      (lvl : int)
      (base : Surface.preterm)
      (j : int)
  : (Surface.preterm * int * op_decl) option
  =
  let rec try_each = function
    | [] -> None
    | op :: rest ->
      (match try_hole_starting_op st op lvl base j with
       | Some (r, j') -> Some (r, j', op)
       | None -> try_each rest)
  in
  try_each ops

(* Match an op whose template starts with a literal (Closed or Prefix).
   Walks the template from position i, consuming literals literally and
   recursively parsing holes. Inner holes at level 0; the final hole of a
   Prefix template is the outer rhs (level given by `level_for_outer_rhs`). *)
and try_lit_starting_op (st : parser_state) (op : op_decl) (lvl : int) (i : int)
  : (Surface.preterm * int) option
  =
  let n = Array.length st.toks in
  let last_hole_idx = last_hole_index op.template in
  let template_arr = Array.of_list op.template in
  let template_len = Array.length template_arr in
  let matches = ref [] in
  let pos = ref i in
  let ok = ref true in
  let k = ref 0 in
  while !ok && !k < template_len do
    let part = template_arr.(!k) in
    match part with
    | Lit s ->
      if
        !pos < n
        &&
        match st.toks.(!pos) with
        | TName (s', _) -> String.equal s s'
        | _ -> false
      then begin
        pos := !pos + 1;
        incr k
      end
      else ok := false
    | Hole _ ->
      let lvl_hole =
        if !k = last_hole_idx && op.shape = Prefix then level_for_outer_rhs op lvl else 0
      in
      (match parse_level st lvl_hole !pos with
       | None -> ok := false
       | Some (m, j') ->
         matches := m :: !matches;
         pos := j';
         incr k)
  done;
  if !ok then Some (lower_body op (List.rev !matches), !pos) else None

(* Match an op whose template starts with a hole (Postfix or Infix). The
   caller passes `base` for that first hole and `j` for the position
   immediately after. Walk the rest of the template from index 1. *)
and try_hole_starting_op
      (st : parser_state)
      (op : op_decl)
      (lvl : int)
      (base : Surface.preterm)
      (j : int)
  : (Surface.preterm * int) option
  =
  let n = Array.length st.toks in
  let last_hole_idx = last_hole_index op.template in
  let template_arr = Array.of_list op.template in
  let template_len = Array.length template_arr in
  let matches = ref [ base ] in
  (* outer lhs already supplied *)
  let pos = ref j in
  let ok = ref true in
  let k = ref 1 in
  while !ok && !k < template_len do
    let part = template_arr.(!k) in
    match part with
    | Lit s ->
      if
        !pos < n
        &&
        match st.toks.(!pos) with
        | TName (s', _) -> String.equal s s'
        | _ -> false
      then begin
        pos := !pos + 1;
        incr k
      end
      else ok := false
    | Hole _ ->
      let lvl_hole =
        if !k = last_hole_idx && op.shape = Infix then level_for_outer_rhs op lvl else 0
      in
      (match parse_level st lvl_hole !pos with
       | None -> ok := false
       | Some (m, j') ->
         matches := m :: !matches;
         pos := j';
         incr k)
  done;
  if !ok then Some (lower_body op (List.rev !matches), !pos) else None

(* Parse a maximal run of atom-like tokens as a left-associative App spine.
   Returns None if the first position is not atom-like. *)
and parse_atom_spine (st : parser_state) (i : int) : (Surface.preterm * int) option =
  let n = Array.length st.toks in
  let to_atom = function
    | TAtom p -> p
    | TName (s, _) -> Surface.Var [ s ]
    | TImpArg _ -> assert false
  in
  let is_atom_start t =
    match t with
    | TAtom _ -> true
    | TName (s, _) -> not (is_op_lit st s)
    | TImpArg _ -> false
  in
  if i >= n || not (is_atom_start st.toks.(i))
  then None
  else (
    let head = to_atom st.toks.(i) in
    let rec loop j acc =
      if j >= n
      then acc, j
      else (
        match st.toks.(j) with
        | TAtom p -> loop (j + 1) (Surface.App (false, acc, p))
        | TName (s, _) when not (is_op_lit st s) ->
          loop (j + 1) (Surface.App (false, acc, Surface.Var [ s ]))
        | TImpArg p -> loop (j + 1) (Surface.App (true, acc, p))
        | _ -> acc, j)
    in
    let result, j = loop (i + 1) head in
    Some (result, j))
;;

let parse_soup (table : op_table) (items : Surface.soup_item list) : Surface.preterm =
  let st = mk_state table items in
  let n = Array.length st.toks in
  match parse_level st 0 0 with
  | Some (term, j) when j = n -> term
  | Some (_term, j) ->
    Reporter.fatalf Parse_error "incomplete operator parse: stopped at token %d of %d" j n
  | None -> Reporter.fatalf Parse_error "no parse for operator soup of length %d" n
;;

let%expect_test "parse_soup: empty table, single atom" =
  let result = parse_soup empty_table [ Surface.SI_Atom (Surface.Var [ "x" ]) ] in
  print_string @@ [%show: Surface.preterm] result;
  [%expect {| x |}]
;;

let%expect_test "parse_soup: empty table, App spine" =
  let result =
    parse_soup
      empty_table
      [ Surface.SI_Name ("f", None)
      ; Surface.SI_Name ("x", None)
      ; Surface.SI_Name ("y", None)
      ]
  in
  print_string @@ [%show: Surface.preterm] result;
  [%expect {| ((f x) y) |}]
;;

let%expect_test "parse_soup: empty table, implicit arg" =
  let result =
    parse_soup
      empty_table
      [ Surface.SI_Name ("f", None)
      ; Surface.SI_Imp_arg (Surface.Var [ "A" ])
      ; Surface.SI_Name ("x", None)
      ]
  in
  print_string @@ [%show: Surface.preterm] result;
  [%expect {| ((f {A}) x) |}]
;;

let%expect_test "parse_soup: binary infix" =
  let plus =
    make_op_decl
      ~template:"\\x + \\y"
      ~body:(Surface.Var [ "add" ])
      ~options:[ Surface.OO_Associativity Surface.OA_Left ]
  in
  let table = add_decl plus empty_table in
  let result =
    parse_soup
      table
      [ Surface.SI_Name ("a", None)
      ; Surface.SI_Name ("+", None)
      ; Surface.SI_Name ("b", None)
      ]
  in
  print_string @@ [%show: Surface.preterm] result;
  [%expect {| ((add a) b) |}]
;;

let%expect_test "parse_soup: precedence — `*` tighter than `+`" =
  let plus =
    make_op_decl
      ~template:"\\x + \\y"
      ~body:(Surface.Var [ "add" ])
      ~options:[ Surface.OO_Associativity Surface.OA_Left ]
  in
  let times =
    make_op_decl
      ~template:"\\x * \\y"
      ~body:(Surface.Var [ "mul" ])
      ~options:
        [ Surface.OO_Stronger_than [ [ "+" ] ]; Surface.OO_Associativity Surface.OA_Left ]
  in
  let table = add_decl times (add_decl plus empty_table) in
  (* 1 + 2 * 3 → add 1 (mul 2 3) *)
  let result =
    parse_soup
      table
      [ Surface.SI_Name ("x1", None)
      ; Surface.SI_Name ("+", None)
      ; Surface.SI_Name ("x2", None)
      ; Surface.SI_Name ("*", None)
      ; Surface.SI_Name ("x3", None)
      ]
  in
  print_string @@ [%show: Surface.preterm] result;
  [%expect {| ((add x1) ((mul x2) x3)) |}]
;;

let%expect_test "parse_soup: ternary mixfix" =
  let ite =
    make_op_decl
      ~template:"if \\x then \\y else \\z"
      ~body:(Surface.Var [ "ite" ])
      ~options:[]
  in
  let table = add_decl ite empty_table in
  let result =
    parse_soup
      table
      [ Surface.SI_Name ("if", None)
      ; Surface.SI_Name ("c", None)
      ; Surface.SI_Name ("then", None)
      ; Surface.SI_Name ("a", None)
      ; Surface.SI_Name ("else", None)
      ; Surface.SI_Name ("b", None)
      ]
  in
  print_string @@ [%show: Surface.preterm] result;
  [%expect {| (((ite c) a) b) |}]
;;

let%expect_test "parse_soup: postfix `!`" =
  let bang =
    make_op_decl ~template:"\\x !" ~body:(Surface.Var [ "factorial" ]) ~options:[]
  in
  let table = add_decl bang empty_table in
  let result =
    parse_soup table [ Surface.SI_Name ("n", None); Surface.SI_Name ("!", None) ]
  in
  print_string @@ [%show: Surface.preterm] result;
  [%expect {| (factorial n) |}]
;;

let%expect_test "parse_soup: prefix `not`" =
  let not_op =
    make_op_decl ~template:"not \\x" ~body:(Surface.Var [ "negate" ]) ~options:[]
  in
  let table = add_decl not_op empty_table in
  let result =
    parse_soup table [ Surface.SI_Name ("not", None); Surface.SI_Name ("b", None) ]
  in
  print_string @@ [%show: Surface.preterm] result;
  [%expect {| (negate b) |}]
;;

let%expect_test "parse_soup: \\associativity \\right" =
  let arrow =
    make_op_decl
      ~template:"\\x ==> \\y"
      ~body:(Surface.Var [ "imp" ])
      ~options:[ Surface.OO_Associativity Surface.OA_Right ]
  in
  let table = add_decl arrow empty_table in
  let result =
    parse_soup
      table
      [ Surface.SI_Name ("a", None)
      ; Surface.SI_Name ("==>", None)
      ; Surface.SI_Name ("b", None)
      ; Surface.SI_Name ("==>", None)
      ; Surface.SI_Name ("c", None)
      ]
  in
  print_string @@ [%show: Surface.preterm] result;
  [%expect {| ((imp a) ((imp b) c)) |}]
;;

(* ===========================================================================
   5. Wiring: build a table from top-forms and lower the whole module.
   ===========================================================================
   Walk the top list in declaration order. Each `Operator_decl` is
   validated and added to the running table. Every other top form is
   lowered using the CURRENT table — operators declared later in the file
   do not affect earlier expressions (declare-before-use). *)

let rec lower_preterm (table : op_table) (t : Surface.preterm) : Surface.preterm =
  match t with
  | Surface.Located lv -> Surface.Located { lv with value = lower_preterm table lv.value }
  | Surface.Op_soup items ->
    (* Recurse into nested soup items first, then resolve the whole soup. *)
    let items' =
      List.map
        (function
          | Surface.SI_Atom p -> Surface.SI_Atom (lower_preterm table p)
          | Surface.SI_Name _ as n -> n
          | Surface.SI_Imp_arg p -> Surface.SI_Imp_arg (lower_preterm table p))
        items
    in
    parse_soup table items'
  | Surface.App (impl, f, x) ->
    Surface.App (impl, lower_preterm table f, lower_preterm table x)
  | Surface.Lambda b -> Surface.Lambda { b with bound = lower_preterm table b.bound }
  | Surface.TypedLambda (b, body) ->
    Surface.TypedLambda
      ({ b with bound = lower_preterm table b.bound }, lower_preterm table body)
  | Surface.Pi (b, body) ->
    Surface.Pi ({ b with bound = lower_preterm table b.bound }, lower_preterm table body)
  | Surface.Max (a, b) -> Surface.Max (lower_preterm table a, lower_preterm table b)
  | Surface.Universe | Surface.Hole | Surface.Goal _ | Surface.Var _ -> t
  | Surface.IdAbsurd p -> Surface.IdAbsurd (lower_preterm table p)
  | Surface.RecordLit entries ->
    Surface.RecordLit (List.map (fun (f, e) -> f, lower_preterm table e) entries)
  | Surface.RecordUpdate (base, entries) ->
    Surface.RecordUpdate
      (lower_preterm table base, List.map (fun (f, e) -> f, lower_preterm table e) entries)
  | Surface.Proj (e, f) -> Surface.Proj (lower_preterm table e, f)
  | Surface.Inline_elim _ as t -> t
;;

let lower_binder (table : op_table) (b : Surface.preterm Violet_kernel.Syntax.binder)
  : Surface.preterm Violet_kernel.Syntax.binder
  =
  { b with bound = lower_preterm table b.bound }
;;

let lower_binders
      (table : op_table)
      (bs : Surface.preterm Violet_kernel.Syntax.binder list)
  : Surface.preterm Violet_kernel.Syntax.binder list
  =
  List.map (lower_binder table) bs
;;

let lower_clause (table : op_table) (c : Surface.clause) : Surface.clause =
  { c with body = lower_preterm table c.body }
;;

(* Lower a non-operator top form using the current table. Operator_decl is
   handled separately by the walker (it consumes the form rather than
   lowering it). *)
let lower_top_with (table : op_table) : Surface.top -> Surface.top = function
  | Surface.Let { name; name_loc; bindings; result_ty; body } ->
    Surface.Let
      { name
      ; name_loc
      ; bindings = lower_binders table bindings
      ; result_ty = lower_preterm table result_ty
      ; body = lower_preterm table body
      }
  | Surface.Data
      { name; name_loc; params; deps; ind_ty; ind_ty_loc; ctors; ctor_name_locs } ->
    Surface.Data
      { name
      ; name_loc
      ; params = lower_binders table params
      ; deps = lower_binders table deps
      ; ind_ty = lower_preterm table ind_ty
      ; ind_ty_loc
      ; ctors = lower_binders table ctors
      ; ctor_name_locs
      }
  | Surface.Stack_def { name; name_loc; params; signature; moves; clauses } ->
    Surface.Stack_def
      { name
      ; name_loc
      ; params = lower_binders table params
      ; signature = lower_preterm table signature
      ; moves
      ; clauses = List.map (lower_clause table) clauses
      }
  | Surface.Elim_def { name; name_loc; params; signature; opens; intros; target; clauses }
    ->
    Surface.Elim_def
      { name
      ; name_loc
      ; params = lower_binders table params
      ; signature = lower_preterm table signature
      ; opens
      ; intros
      ; target
      ; clauses = List.map (lower_clause table) clauses
      }
  | Surface.Universe_decl _ as u -> u
  | Surface.Operator_decl _ ->
    Reporter.fatalf
      Elab_error
      "internal: lower_top_with should not be called on Operator_decl"
  | Surface.Record { name; name_loc; params; ind_ty; fields } ->
    let lower_binders' =
      List.map (fun b -> { b with Surface.bound = lower_preterm table b.Surface.bound })
    in
    Surface.Record
      { name
      ; name_loc
      ; params = lower_binders' params
      ; ind_ty = lower_preterm table ind_ty
      ; fields = lower_binders' fields
      }
;;

(* Cross-module flow: each module's exported operator table is recorded
   here under its module name (the file's basename without extension). When
   another module imports it, we look the table up and merge it into the
   importer's starting table. Conflicts (same template, different bodies)
   error at import time. *)
let module_op_tables : (string, op_table) Hashtbl.t = Hashtbl.create 32
let module_name_of_path (p : Yuujinchou.Trie.path) : string = String.concat "/" p

(* Merge another table's decls into ours. Duplicate-template across modules
   raises unless the duplicates share an origin (diamond import). *)
let merge_table (target : op_table) (source : op_table) : op_table =
  List.fold_left (fun acc d -> merge_decl d acc) target (List.rev source.decls)
;;

(* Walk the top list in order, threading the operator table. Operator
   declarations are consumed by this pass (validated and added to the
   table) and dropped from the output — downstream elab never sees them.
   Imports contribute their exported tables to the starting table. *)
let resolve_module ?module_name (file : Surface.t) : Surface.t =
  let module_name =
    match module_name with
    | Some n -> n
    | None -> Filename.chop_extension @@ Filename.basename file.name
  in
  let init_table =
    List.fold_left
      (fun acc import_path ->
         let name = module_name_of_path import_path in
         match Hashtbl.find_opt module_op_tables name with
         | None -> acc (* imported module has no operators; nothing to merge *)
         | Some t -> merge_table acc t)
      empty_table
      file.imports
  in
  let table = ref init_table in
  let tops' =
    List.filter_map
      (fun (top : Surface.top Asai.Range.located) ->
         match top.value with
         | Surface.Operator_decl { template; body; options } ->
           (* Lower the body with the CURRENT table (before adding this op). *)
           let body' = lower_preterm !table body in
           let decl =
             { (make_op_decl ~template ~body:body' ~options) with origin = module_name }
           in
           table := add_decl decl !table;
           None
         | _ -> Some { top with Asai.Range.value = lower_top_with !table top.value })
      file.tops
  in
  (* Force a final validation of the assembled table - cycle detection,
     topological consistency. This catches errors even in files that don't
     use the operators in any expression. *)
  let _ = compute_levels !table in
  (* Register the final table for downstream modules to import. *)
  Hashtbl.replace module_op_tables module_name !table;
  { file with tops = tops' }
;;

(* For REPL / external single-expression use: look up the op table registered
   by a previous `resolve_module` pass, and lower a fresh preterm with it. *)
let resolve_preterm_for_module ~(module_name : string) (t : Surface.preterm)
  : Surface.preterm
  =
  let table =
    match Hashtbl.find_opt module_op_tables module_name with
    | Some t -> t
    | None -> empty_table
  in
  lower_preterm table t
;;

let%expect_test "resolve_module: operator then let — soup uses operator, decl consumed" =
  let mk_op : Surface.top Asai.Range.located =
    { loc = None
    ; value =
        Surface.Operator_decl
          { template = "\\x + \\y"
          ; body = Surface.Var [ "add" ]
          ; options = [ Surface.OO_Associativity Surface.OA_Left ]
          }
    }
  in
  let mk_let : Surface.top Asai.Range.located =
    { loc = None
    ; value =
        Surface.Let
          { name = "two"
          ; name_loc = None
          ; bindings = []
          ; result_ty = Surface.Op_soup [ Surface.SI_Name ("Nat", None) ]
          ; body =
              Surface.Op_soup
                [ Surface.SI_Name ("one", None)
                ; Surface.SI_Name ("+", None)
                ; Surface.SI_Name ("one", None)
                ]
          }
    }
  in
  let file : Surface.t =
    { name = "test.vt"; imports = []; exports = []; tops = [ mk_op; mk_let ] }
  in
  let result = resolve_module file in
  let printed = List.map (fun lt -> lt.Asai.Range.value) result.tops in
  print_string @@ [%show: Surface.top list] printed;
  [%expect
    {|
    [Surface.Let {name = "two"; name_loc = None; bindings = []; result_ty = Nat;
       body = ((add one) one)}
      ]
    |}]
;;

let%expect_test "resolve_module: diamond import of common library does not duplicate" =
  Hashtbl.clear module_op_tables;
  let mk_op : Surface.top Asai.Range.located =
    { loc = None
    ; value =
        Surface.Operator_decl
          { template = "\\x = \\y"
          ; body = Surface.Var [ "Id" ]
          ; options = [ Surface.OO_Associativity Surface.OA_Left ]
          }
    }
  in
  (* Module A: declares the operator. *)
  let a : Surface.t =
    { name = "diamond_a.vt"; imports = []; exports = []; tops = [ mk_op ] }
  in
  let _ = resolve_module a in
  (* Module B: imports A but declares nothing of its own. *)
  let b : Surface.t =
    { name = "diamond_b.vt"; imports = [ [ "diamond_a" ] ]; exports = []; tops = [] }
  in
  let _ = resolve_module b in
  (* Module C: imports BOTH A and B — same operator arrives via two paths. *)
  let c : Surface.t =
    { name = "diamond_c.vt"
    ; imports = [ [ "diamond_a" ]; [ "diamond_b" ] ]
    ; exports = []
    ; tops = []
    }
  in
  let _ = resolve_module c in
  print_string "ok";
  [%expect {| ok |}]
;;

let%expect_test "resolve_module: same template from two distinct modules still conflicts" =
  Hashtbl.clear module_op_tables;
  let mk_op body =
    { Asai.Range.loc = None
    ; value =
        Surface.Operator_decl
          { template = "\\x + \\y"
          ; body = Surface.Var [ body ]
          ; options = [ Surface.OO_Associativity Surface.OA_Left ]
          }
    }
  in
  (* Two unrelated modules each declare `~x + ~y` for different operations. *)
  let a : Surface.t =
    { name = "conflict_a.vt"; imports = []; exports = []; tops = [ mk_op "add_a" ] }
  in
  let _ = resolve_module a in
  let b : Surface.t =
    { name = "conflict_b.vt"; imports = []; exports = []; tops = [ mk_op "add_b" ] }
  in
  let _ = resolve_module b in
  (* Importing both should be a genuine conflict, not a silent dedupe. *)
  let c : Surface.t =
    { name = "conflict_c.vt"
    ; imports = [ [ "conflict_a" ]; [ "conflict_b" ] ]
    ; exports = []
    ; tops = []
    }
  in
  (try
     let _ = resolve_module c in
     print_string "UNEXPECTED: no error"
   with
   | _ -> print_string "got conflict");
  [%expect {| got conflict |}]
;;
