module Message = struct
  type t =
    | IO_error
    | Parse_error
    | NoVar_error
    | Type_error
    | Elab_error
    | Eval_error
    | TODO
    | Goal_report
    | Goal_unresolved
  [@@deriving show]

  let default_severity : t -> Asai.Diagnostic.severity = function
    | IO_error | Parse_error | NoVar_error | Type_error | Elab_error | Eval_error -> Error
    | TODO -> Warning
    | Goal_report -> Info
    | Goal_unresolved -> Warning
  ;;

  let short_code : t -> string = show
end

include Asai.Reporter.Make (Message)
