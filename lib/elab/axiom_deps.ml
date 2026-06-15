module Syntax = Violet_kernel.Syntax
open Syntax
module Trie = Yuujinchou.Trie

(* A name's identity is its complete Yuujinchou id — a [Trie.path] (the same
   thing carried by [Observer.Def.path]). The serialized "/"-joined form of a
   path is exactly what appears as a [Core.Var] head, so we use it as the
   internal Hashtbl key while exposing genuine paths at the API boundary. *)
let key (p : Trie.path) : string = Syntax.Name.of_segments p

module PathSet = Set.Make (struct
    type t = Trie.path

    let compare = compare
  end)

let registry : (string, PathSet.t) Hashtbl.t = Hashtbl.create ~random:true 256
let reset () = Hashtbl.clear registry

let deps_set (p : Trie.path) : PathSet.t =
  match Hashtbl.find_opt registry (key p) with
  | Some s -> s
  | None -> PathSet.empty
;;

let register_axiom (p : Trie.path) : unit =
  Hashtbl.replace registry (key p) (PathSet.singleton p)
;;

let register_def (p : Trie.path) ~(refs : Trie.path list) : unit =
  let union =
    List.fold_left (fun acc r -> PathSet.union acc (deps_set r)) PathSet.empty refs
  in
  Hashtbl.replace registry (key p) union
;;

let deps_of (p : Trie.path) : Trie.path list = PathSet.elements (deps_set p)

(* [deps_of] with [p] itself dropped — what surfaces (hover, REPL, goal
   reports, Def events) show, since a definition listing itself as a
   dependency is noise. *)
let display_deps_of (p : Trie.path) : Trie.path list =
  List.filter (fun d -> d <> p) (deps_of p)
;;

(* Every global [Core.Var] head occurring in [t], each as its complete id.
   A head is the "/"-joined serialization of a path, so we split it back. *)
let rec refs_in_term (t : Core.term) : Trie.path list =
  match t with
  | Core.Var name -> [ Syntax.Name.to_segments name ]
  | Core.Universe _ | Core.LocalVar _ | Core.Meta _ | Core.InsertedMeta _ | Core.Empty ->
    []
  | Core.App (a, b, _) -> refs_in_term a @ refs_in_term b
  | Core.Lambda { bound; _ } -> refs_in_term bound
  | Core.TypedLambda ({ bound; _ }, body) -> refs_in_term bound @ refs_in_term body
  | Core.Pi ({ bound; _ }, b) -> refs_in_term bound @ refs_in_term b
  | Core.Lift { ty; _ } -> refs_in_term ty
  | Core.LiftTerm { ty; tm; _ } | Core.UnliftTerm { ty; tm; _ } ->
    refs_in_term ty @ refs_in_term tm
  | Core.RecordType { params; fields; _ } ->
    List.concat_map refs_in_term params
    @ List.concat_map (fun (b : Core.term Syntax.binder) -> refs_in_term b.bound) fields
  | Core.RecordIntro { fields; _ } ->
    List.concat_map (fun (_, t) -> refs_in_term t) fields
  | Core.RecordProj { record; _ } -> refs_in_term record
  | Core.IdAbsurd t -> refs_in_term t
  | Core.Absurd t -> refs_in_term t
;;

(* test helper: render a path list as comma-joined "/"-paths *)
let show_paths (ps : Trie.path list) : string =
  String.concat "," (List.map Syntax.Name.of_segments ps)
;;

let%expect_test "direct axiom dependency" =
  reset ();
  register_axiom [ "ua" ];
  register_def [ "foo" ] ~refs:[ [ "ua" ] ];
  print_string (show_paths (deps_of [ "foo" ]));
  [%expect {| ua |}]
;;

let%expect_test "transitive dependency through a chain" =
  reset ();
  register_axiom [ "ua" ];
  register_def [ "foo" ] ~refs:[ [ "ua" ] ];
  register_def [ "bar" ] ~refs:[ [ "foo" ] ];
  print_string (show_paths (deps_of [ "bar" ]));
  [%expect {| ua |}]
;;

let%expect_test "diamond dedupes" =
  reset ();
  register_axiom [ "ua" ];
  register_def [ "left" ] ~refs:[ [ "ua" ] ];
  register_def [ "right" ] ~refs:[ [ "ua" ] ];
  register_def [ "join" ] ~refs:[ [ "left" ]; [ "right" ] ];
  print_string (show_paths (deps_of [ "join" ]));
  [%expect {| ua |}]
;;

let%expect_test "two axioms accumulate, sorted" =
  reset ();
  register_axiom [ "funext" ];
  register_axiom [ "ua" ];
  register_def [ "foo" ] ~refs:[ [ "ua" ]; [ "funext" ] ];
  print_string (show_paths (deps_of [ "foo" ]));
  [%expect {| funext,ua |}]
;;

let%expect_test "axiom-free definition has no deps" =
  reset ();
  register_def [ "plain" ] ~refs:[ [ "nat" ]; [ "succ" ] ];
  print_string
    (match deps_of [ "plain" ] with
     | [] -> "<none>"
     | xs -> show_paths xs);
  [%expect {| <none> |}]
;;

let%expect_test "refs_in_term collects Var heads as complete ids" =
  reset ();
  (* a bare head and a "/"-joined (qualified) head both become full paths *)
  let t = Core.App (Core.Var "ua", Core.Var "Mod/x", false) in
  print_string (show_paths (refs_in_term t));
  [%expect {| ua,Mod/x |}]
;;

(* Mirrors how elab_data wires inductive/constructor axiom tracking: the
   inductive registers from its type's refs; each constructor inherits the
   inductive (the explicit [data_name] ref) plus refs in its own type; a
   definition using the constructor transitively reports the axiom. The
   constructor's complete id is the path [Box; wrap], matching its "Box/wrap"
   Var head. *)
let%expect_test "constructor inherits inductive's axioms via explicit data ref" =
  reset ();
  register_axiom [ "ua" ];
  (* \data Box : U  (type does NOT mention ua) *)
  register_def [ "Box" ] ~refs:(refs_in_term (Core.Var "U"));
  (* | wrap : ua -> Box  (ctor type mentions ua; @ [["Box"]] inherits the data) *)
  register_def
    [ "Box"; "wrap" ]
    ~refs:
      (refs_in_term
         (Core.Pi
            ({ name = Anon; bound = Core.Var "ua"; implicit = false }, Core.Var "Box"))
       @ [ [ "Box" ] ]);
  (* \let use : Box => Box/wrap …  — refs the constructor by its full id *)
  register_def [ "use" ] ~refs:[ [ "Box"; "wrap" ] ];
  Printf.printf
    "Box=[%s] wrap=[%s] use=[%s]"
    (show_paths (deps_of [ "Box" ]))
    (show_paths (deps_of [ "Box"; "wrap" ]))
    (show_paths (deps_of [ "use" ]));
  [%expect {| Box=[] wrap=[ua] use=[ua] |}]
;;
