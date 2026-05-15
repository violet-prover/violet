(* find_root start_dir = Some dir if dir or some ancestor contains info.vt *)
let rec find_root (dir : string) : string option =
  let candidate = Filename.concat dir "info.vt" in
  if Sys.file_exists candidate
  then Some dir
  else (
    let parent = Filename.dirname dir in
    if parent = dir then None (* hit filesystem root *) else find_root parent)
;;

let%expect_test "find_root finds info.vt in same dir" =
  let tmp = Filename.temp_dir "violet_test_" "" in
  let info = Filename.concat tmp "info.vt" in
  let oc = open_out info in
  output_string oc "";
  close_out oc;
  (match find_root tmp with
   | Some d -> Printf.printf "found=%b" (d = tmp)
   | None -> print_string "not found");
  [%expect {| found=true |}]
;;

let%expect_test "find_root walks up" =
  let tmp = Filename.temp_dir "violet_test_" "" in
  let info = Filename.concat tmp "info.vt" in
  let oc = open_out info in
  output_string oc "";
  close_out oc;
  let nested = Filename.concat tmp "src/sub" in
  Unix.mkdir (Filename.concat tmp "src") 0o755;
  Unix.mkdir nested 0o755;
  (match find_root nested with
   | Some d -> Printf.printf "found=%b" (d = tmp)
   | None -> print_string "not found");
  [%expect {| found=true |}]
;;

let%expect_test "find_root returns None outside any project" =
  let tmp = Filename.temp_dir "violet_test_" "" in
  (* no info.vt under tmp *)
  (match find_root tmp with
   | Some _ -> print_string "unexpected hit"
   | None -> print_string "not found");
  [%expect {| not found |}]
;;
