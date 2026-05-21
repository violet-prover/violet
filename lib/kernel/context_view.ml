open Bwd

type t =
  { names : string bwd
  ; lvl : int
  }

let empty = { names = Emp; lvl = 0 }
let make ~names ~lvl = { names; lvl }
let extend t name = { names = Snoc (t.names, name); lvl = t.lvl + 1 }
let lvl t = t.lvl

let nth_name_from_lvl t lvl =
  if lvl >= 0 && lvl < t.lvl then Some (Bwd.nth t.names (t.lvl - 1 - lvl)) else None
;;

let%expect_test "empty has lvl 0 and no names" =
  let t = empty in
  Printf.printf
    "lvl=%d, nth=%s"
    (lvl t)
    (match nth_name_from_lvl t 0 with
     | Some n -> n
     | None -> "<none>");
  [%expect {| lvl=0, nth=<none> |}]
;;

let%expect_test "extend appends innermost-last; nth_name_from_lvl reads outermost-first" =
  let t = extend (extend empty "x") "y" in
  Printf.printf
    "lvl=%d, [0]=%s, [1]=%s, [2]=%s"
    (lvl t)
    (Option.value (nth_name_from_lvl t 0) ~default:"<none>")
    (Option.value (nth_name_from_lvl t 1) ~default:"<none>")
    (Option.value (nth_name_from_lvl t 2) ~default:"<none>");
  [%expect {| lvl=2, [0]=x, [1]=y, [2]=<none> |}]
;;
