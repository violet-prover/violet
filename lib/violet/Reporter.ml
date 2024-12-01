module Message = struct
  type t =
    | IO_error
    | Parse_error
    | NoVar_error
    | Type_error
    | Elab_error
    | Eval_error
    | TODO
  [@@deriving show]

  let default_severity : t -> Asai.Diagnostic.severity = function
    | IO_error | Parse_error | NoVar_error | Type_error | Elab_error | Eval_error -> Error
    | TODO -> Warning
  ;;

  let short_code : t -> string = show
end

include Asai.Reporter.Make (Message)
