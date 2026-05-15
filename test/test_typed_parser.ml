(* Parser unit tests for typed-algebraic parser combinators.
   Tests correctness of specific parsing constructs. *)

let positive_test () =
  Violet_elab.Reporter.run ~emit:(fun _ -> ()) ~fatal:(fun _ -> exit 1)
  @@ fun () ->
  let parse_tops src =
    let lexbuf = Lexing.from_string src in
    let toks = Array.of_list (Violet_elab.Parser.tokens "<positive_test>" lexbuf) in
    let m = Violet_elab.Parser.parse_buf ~name:"<positive_test>" toks in
    m.Violet_elab.Surface.tops
  in
  (* Basic let binding parses OK *)
  let tops = parse_tops "\\let f : U -> U => \\x -> x\n" in
  match tops with
  | [ _ ] -> Format.printf "positive_test OK@."
  | _ ->
    Format.printf "positive_test FAIL@.";
    exit 1
;;

let goal_test () =
  Violet_elab.Reporter.run ~emit:(fun _ -> ()) ~fatal:(fun _ -> exit 1)
  @@ fun () ->
  let parse_tops src =
    let lexbuf = Lexing.from_string src in
    let toks = Array.of_list (Violet_elab.Parser.tokens "<goal_test>" lexbuf) in
    let m = Violet_elab.Parser.parse_buf ~name:"<goal_test>" toks in
    m.Violet_elab.Surface.tops
  in
  (* Elim-style where-clause parses OK *)
  let tops =
    parse_tops "\\let neg2 : U -> U \\where\n  neg2 b <= \\elim b\n  | neg2 x => x\n"
  in
  match tops with
  | [ _ ] -> Format.printf "goal_test OK@."
  | _ ->
    Format.printf "goal_test FAIL@.";
    exit 1
;;

let elim_intro_test () =
  Violet_elab.Reporter.run ~emit:(fun _ -> ()) ~fatal:(fun _ -> exit 1)
  @@ fun () ->
  let parse_tops src =
    let lexbuf = Lexing.from_string src in
    let toks = Array.of_list (Violet_elab.Parser.tokens "<elim_test>" lexbuf) in
    let m = Violet_elab.Parser.parse_buf ~name:"<elim_test>" toks in
    m.Violet_elab.Surface.tops
  in
  (* Bare intros — all explicit *)
  let tops1 =
    parse_tops "\\let f : (x : U) -> U \\where\n  f x <= \\elim x\n  | f x => x\n"
  in
  (match tops1 with
   | [ { Asai.Range.value =
           Violet_elab.Surface.Elim_def
             { intros = [ ("x", false) ]
             ; clauses = [ { patterns = [ Violet_elab.Surface.PVar "x" ]; _ } ]
             ; _
             }
       ; _
       }
     ] -> Format.printf "elim_intro_test OK  bare intros@."
   | _ ->
     Format.printf "elim_intro_test FAIL bare intros@.";
     exit 1);
  (* Bracketed intros — implicit + explicit *)
  let tops2 =
    parse_tops "\\let f : (x : U) -> U \\where\n  f {A} x <= \\elim x\n  | f x => x\n"
  in
  (match tops2 with
   | [ { Asai.Range.value =
           Violet_elab.Surface.Elim_def { intros = [ ("A", true); ("x", false) ]; _ }
       ; _
       }
     ] -> Format.printf "elim_intro_test OK  bracketed intros@."
   | _ ->
     Format.printf "elim_intro_test FAIL bracketed intros@.";
     exit 1);
  (* PImpVar in clause patterns *)
  let tops3 =
    parse_tops "\\let f : (x : U) -> U \\where\n  f x <= \\elim x\n  | f {A} x => x\n"
  in
  match tops3 with
  | [ { Asai.Range.value =
          Violet_elab.Surface.Elim_def
            { clauses =
                [ { patterns =
                      [ Violet_elab.Surface.PImpVar "A"; Violet_elab.Surface.PVar "x" ]
                  ; _
                  }
                ]
            ; _
            }
      ; _
      }
    ] -> Format.printf "elim_intro_test OK  PImpVar clause@."
  | _ ->
    Format.printf "elim_intro_test FAIL PImpVar clause@.";
    exit 1
;;

let benchmark () = Format.printf "benchmark: skipped in unit-test mode@."

let () =
  positive_test ();
  goal_test ();
  elim_intro_test ();
  benchmark ()
;;
