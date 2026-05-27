open Bwd
module Surface = Violet_surface.Surface
module Parser = Violet_surface.Parser
module Op_resolver = Violet_surface.Op_resolver
module Elab = Violet_elab.Elab
module ElabREPL = Violet_elab.Repl
module Evaluation = Violet_elab.Wiring.Eval
module Reporter = Violet_surface.Reporter
module Context = Violet_elab.Context
module Env = Violet_elab.Env
module Tty = Asai.Tty.Make (Reporter.Message)

let prompt = "> "
let history_file = Filename.concat (Sys.getenv "HOME") ".violet_history"

let apply_visibility ~(module_path : string list) ~(imports : string list list) =
  let open Yuujinchou.Language in
  let expose path =
    Context.S.modify_visible (union [ all; renaming path [] ]);
    Env.S.modify_visible (union [ all; renaming path [] ])
  in
  (* Entry module's own decls live under `module_path/...` after check_module
     merged them up. Rename onto the root so the user can type bare names. *)
  expose module_path;
  (* Each import was visible (root + qualified) inside the original section;
     mirror that here. *)
  List.iter expose imports
;;

let visible_names () : string list =
  let visible = Context.S.get_visible () in
  let names = ref [] in
  Yuujinchou.Trie.iter
    (fun path _ -> names := String.concat "/" (Bwd.to_list path) :: !names)
    visible;
  List.sort String.compare !names
;;

let print_browse () =
  let visible = Context.S.get_visible () in
  let entries = ref [] in
  Yuujinchou.Trie.iter
    (fun path (ty, _tag) ->
       let name = String.concat "/" (Bwd.to_list path) in
       entries := (name, ty) :: !entries)
    visible;
  let sorted = List.sort (fun (a, _) (b, _) -> String.compare a b) !entries in
  List.iter
    (fun (name, ty) -> Printf.printf "  %s : %s\n" name (ElabREPL.pretty_repl_value ty))
    sorted;
  Printf.printf "%!"
;;

let commands = [ "\\quit"; "\\type"; "\\browse"; "\\normalize"; "\\open" ]

(* Identifier characters in Violet match the parser's `ident` token: anything
   that isn't whitespace, brackets, or a path separator boundary. The token
   boundary chosen here is conservative — split on whitespace and the
   delimiters that always end a term atom. The `/` inside a qualified name
   stays inside the word so `Nat/z<TAB>` can complete to `Nat/zero`. *)
let is_word_boundary c =
  match c with
  | ' ' | '\t' | '(' | ')' | '{' | '}' | ',' -> true
  | _ -> false
;;

let last_word (s : string) : int * string =
  let n = String.length s in
  let rec find i = if i <= 0 || is_word_boundary s.[i - 1] then i else find (i - 1) in
  let start = find n in
  start, String.sub s start (n - start)
;;

let starts_with ~prefix s =
  let lp = String.length prefix in
  String.length s >= lp && String.sub s 0 lp = prefix
;;

let make_completion_callback (names : string list ref) input completions =
  let start, word = last_word input in
  let pool = if String.length word > 0 && word.[0] = '\\' then commands else !names in
  let prefix_in_buffer = String.sub input 0 start in
  List.iter
    (fun cand ->
       if starts_with ~prefix:word cand
       then LNoise.add_completion completions (prefix_in_buffer ^ cand))
    pool
;;

(* Strip a leading word and return (word, rest). The word is everything up to
   the first whitespace; rest is the trimmed remainder. *)
let split_head (s : string) : string * string =
  let n = String.length s in
  let rec find_space i =
    if i >= n || s.[i] = ' ' || s.[i] = '\t' then i else find_space (i + 1)
  in
  let i = find_space 0 in
  String.sub s 0 i, String.trim (String.sub s i (n - i))
;;

type action =
  | Quit
  | Browse
  | Eval of string
  | Type_of of string
  | Open of string list
  | Unknown of string

let parse_command (line : string) : action option =
  let trimmed = String.trim line in
  if trimmed = ""
  then None
  else if trimmed.[0] = '\\'
  then begin
    let head, rest = split_head trimmed in
    match head with
    | "\\quit" -> Some Quit
    | "\\browse" -> Some Browse
    | "\\type" -> Some (Type_of rest)
    | "\\normalize" -> Some (Eval rest)
    | "\\open" -> Some (Open (String.split_on_char '/' rest))
    | other -> Some (Unknown other)
  end
  else Some (Eval trimmed)
;;

(* Run a thunk with a non-fatal reporter so a per-line error keeps the REPL
   alive. Diagnostics are printed via the same TTY display used elsewhere.
   Uses `try_with` so handlers nest cleanly inside the outer Reporter.run
   that main.ml established. *)
let with_repl_reporter (k : unit -> unit) : unit =
  try Reporter.run ~emit:Tty.display ~fatal:(fun d -> Tty.display d) k with
  | Failure msg -> Printf.printf "%s\n%!" msg
  | exn -> Printf.printf "internal error: %s\n%!" (Printexc.to_string exn)
;;

let handle_eval ~(module_name : string) (src : string) : unit =
  let p = Parser.parse_expression_string ~source:"<repl>" src in
  let p = Op_resolver.resolve_preterm_for_module ~module_name p in
  let tm, ty = ElabREPL.infer_expression ~module_name p in
  let v = Evaluation.eval Bwd.Emp tm in
  Printf.printf
    "%s : %s\n%!"
    (ElabREPL.pretty_repl_value v)
    (ElabREPL.pretty_repl_value ty)
;;

let handle_type ~(module_name : string) (src : string) : unit =
  let p = Parser.parse_expression_string ~source:"<repl>" src in
  let p = Op_resolver.resolve_preterm_for_module ~module_name p in
  let _, ty = ElabREPL.infer_expression ~module_name p in
  Printf.printf "%s\n%!" (ElabREPL.pretty_repl_value ty)
;;

let handle_open (path : string list) : unit =
  match path with
  | [] | [ "" ] -> Printf.printf "usage: \\open PATH (e.g. \\open std/nat)\n%!"
  | _ ->
    let open Yuujinchou.Language in
    Context.S.modify_visible (union [ all; renaming path [] ]);
    Env.S.modify_visible (union [ all; renaming path [] ]);
    Printf.printf "opened %s\n%!" (String.concat "/" path)
;;

let run ~(entry_module : Surface.t) : unit =
  let module_path = [ Filename.chop_extension @@ Filename.basename entry_module.name ] in
  let module_name = String.concat "/" module_path in
  apply_visibility ~module_path ~imports:entry_module.imports;
  let names = ref (visible_names ()) in
  LNoise.set_completion_callback (make_completion_callback names);
  let _ = LNoise.history_load ~filename:history_file in
  let _ = LNoise.history_set ~max_length:1000 in
  Printf.printf
    "Violet REPL — loaded `%s`. \\quit to exit, \\browse to list names, \\type EXPR for \
     the type, \\open PATH to open a namespace.\n\
     %!"
    module_name;
  let rec loop () =
    match LNoise.linenoise prompt with
    | None -> print_endline ""
    | Some raw_line ->
      let _ = LNoise.history_add raw_line in
      let _ = LNoise.history_save ~filename:history_file in
      (match parse_command raw_line with
       | None -> loop ()
       | Some Quit -> ()
       | Some Browse ->
         with_repl_reporter (fun () -> print_browse ());
         loop ()
       | Some (Eval src) ->
         with_repl_reporter (fun () -> handle_eval ~module_name src);
         loop ()
       | Some (Type_of src) ->
         with_repl_reporter (fun () -> handle_type ~module_name src);
         loop ()
       | Some (Open path) ->
         with_repl_reporter (fun () ->
           handle_open path;
           names := visible_names ());
         loop ()
       | Some (Unknown cmd) ->
         Printf.printf "unknown command: %s\n%!" cmd;
         loop ())
  in
  loop ()
;;
