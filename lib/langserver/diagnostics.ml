let lsp_severity (sev : Asai.Diagnostic.severity)
  : Linol_lsp.Lsp.Types.DiagnosticSeverity.t
  =
  match sev with
  | Error -> Error
  | Warning -> Warning
  | Info -> Information
  | Hint -> Hint
  | Bug -> Error
;;

let lsp_range_of_asai (loc : Asai.Range.t) : Linol_lsp.Lsp.Types.Range.t =
  let pos_of (p : Asai.Range.position) =
    Linol_lsp.Lsp.Types.Position.create
      ~line:(p.line_num - 1)
      ~character:(p.offset - p.start_of_line)
  in
  match Asai.Range.split loc with
  | s, e -> Linol_lsp.Lsp.Types.Range.create ~start:(pos_of s) ~end_:(pos_of e)
  | exception Invalid_argument _ ->
    let zero = Linol_lsp.Lsp.Types.Position.create ~line:0 ~character:0 in
    Linol_lsp.Lsp.Types.Range.create ~start:zero ~end_:zero
;;

let lsp_of_asai (d : Violet_common.Reporter.Message.t Asai.Diagnostic.t)
  : Linol_lsp.Lsp.Types.Diagnostic.t
  =
  let range =
    match d.explanation.loc with
    | Some loc -> lsp_range_of_asai loc
    | None ->
      let zero = Linol_lsp.Lsp.Types.Position.create ~line:0 ~character:0 in
      Linol_lsp.Lsp.Types.Range.create ~start:zero ~end_:zero
  in
  let message =
    let buf = Buffer.create 128 in
    let fmt = Format.formatter_of_buffer buf in
    Format.fprintf fmt "%t" d.explanation.value;
    Format.pp_print_flush fmt ();
    Buffer.contents buf
  in
  Linol_lsp.Lsp.Types.Diagnostic.create
    ~range
    ~severity:(lsp_severity d.severity)
    ~code:(`String (Violet_common.Reporter.Message.short_code d.message))
    ~source:"violet"
    ~message:(`String message)
    ()
;;

let%expect_test "severity mapping" =
  let to_s sev =
    Linol_lsp.Lsp.Types.DiagnosticSeverity.yojson_of_t (lsp_severity sev)
    |> Yojson.Safe.to_string
  in
  Printf.printf
    "%s/%s/%s/%s"
    (to_s Asai.Diagnostic.Error)
    (to_s Asai.Diagnostic.Warning)
    (to_s Asai.Diagnostic.Info)
    (to_s Asai.Diagnostic.Hint);
  [%expect {| 1/2/3/4 |}]
;;
