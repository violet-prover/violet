open Syntax

type decl =
  | Let of
      { ty : Core.term
      ; body : Core.term
      }
  | Data of
      { ty : Core.term
      ; ctor_names : string list
      }
  | Ctor of
      { data : string
      ; ty : Core.term
      }
  | Elim of
      { ty : Core.term
      ; reducer : Core.elim_head
      }
  | Axiom of { ty : Core.term }

let show_decl = function
  | Let _ -> "let"
  | Data _ -> "data"
  | Ctor _ -> "ctor"
  | Elim _ -> "elim"
  | Axiom _ -> "axiom"
;;

type t = (string, decl) Hashtbl.t

let create () : t = Hashtbl.create 256

let declare (m : t) (name : string) (d : decl) : unit =
  match Hashtbl.find_opt m name with
  | Some _ -> raise (Error.Kernel_error (Error.DuplicateDecl name))
  | None -> Hashtbl.add m name d
;;

let lookup (m : t) (name : string) : decl option = Hashtbl.find_opt m name

let%expect_test "declare then lookup returns the decl" =
  let m = create () in
  let u : Core.term = Core.Universe Level.LZero in
  declare m "foo" (Let { ty = u; body = u });
  (match lookup m "foo" with
   | Some d -> Printf.printf "found: %s" (show_decl d)
   | None -> Printf.printf "not found");
  [%expect {| found: let |}]
;;

let%expect_test "lookup of unknown name is None" =
  let m = create () in
  (match lookup m "nope" with
   | Some _ -> Printf.printf "found (bug)"
   | None -> Printf.printf "none");
  [%expect {| none |}]
;;

let%expect_test "duplicate declare raises Kernel_error DuplicateDecl" =
  let m = create () in
  let u : Core.term = Core.Universe Level.LZero in
  declare m "foo" (Let { ty = u; body = u });
  (try
     declare m "foo" (Let { ty = u; body = u });
     print_string "no error (bug)"
   with
   | Error.Kernel_error (Error.DuplicateDecl n) -> Printf.printf "dup: %s" n);
  [%expect {| dup: foo |}]
;;

let%expect_test "two independent modules don't collide" =
  let m1 = create () in
  let m2 = create () in
  let u : Core.term = Core.Universe Level.LZero in
  declare m1 "foo" (Let { ty = u; body = u });
  declare m2 "foo" (Let { ty = u; body = u });
  (match lookup m1 "foo", lookup m2 "foo" with
   | Some _, Some _ -> print_string "both present"
   | _ -> print_string "missing");
  [%expect {| both present |}]
;;

let%expect_test "declare an axiom then look it up" =
  let m = create () in
  let u : Core.term = Core.Universe Level.LZero in
  declare m "ua" (Axiom { ty = u });
  (match lookup m "ua" with
   | Some d -> Printf.printf "found: %s" (show_decl d)
   | None -> Printf.printf "not found");
  [%expect {| found: axiom |}]
;;
