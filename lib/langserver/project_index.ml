type t = (string, Violet_interactive.Index.t) Hashtbl.t

let create () : t = Hashtbl.create 64
let update (t : t) ~file ~index = Hashtbl.replace t file index

let find_by_file (t : t) ~file : Violet_interactive.Index.t option =
  Hashtbl.find_opt t file
;;

let%expect_test "update and find round-trip" =
  let t = create () in
  let idx = Violet_interactive.Index.empty in
  update t ~file:"/tmp/Foo.vt" ~index:idx;
  Printf.printf "found=%b" (Option.is_some (find_by_file t ~file:"/tmp/Foo.vt"));
  [%expect {| found=true |}]
;;

let%expect_test "find missing returns None" =
  let t = create () in
  Printf.printf "found=%b" (Option.is_some (find_by_file t ~file:"/tmp/Missing.vt"));
  [%expect {| found=false |}]
;;
