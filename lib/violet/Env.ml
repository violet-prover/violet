open Yuujinchou
open Bwd
open Syntax

type modifier_cmd = Trace

module ValueEnvironment = struct
  type data = Core.value

  (* Locals don't live in Yuujinchou anymore — they're handled in Checker's
     local_ctx with de Bruijn indices.  Only globals remain here. *)
  type tag =
    [ `Imported
    | `Constructor
    ]

  type hook = modifier_cmd

  type context =
    [ `Visible
    | `Export
    ]
end

module S = Scope.Make (ValueEnvironment)

let lookup (x : string) : Core.value =
  match S.resolve [ x ] with
  | Some (v, _) -> v
  | None ->
    Reporter.fatalf
      NoVar_error
      "cannot find `%s` in environment"
      (String.concat "." [ x ])
;;

(* Top-level let definitions, keyed by name.  Unification consults this when
   it needs to unfold a `Var (x, _)` opaque head.  Constructors and inductive
   types live in Yuujinchou (S) only — they're not "defined" in the same sense. *)
let definitions : (string, Core.value) Hashtbl.t = Hashtbl.create ~random:true 100

let register_definition (name : string) (v : Core.value) : unit =
  Hashtbl.replace definitions name v
;;

let unfold_def (name : string) : Core.value option = Hashtbl.find_opt definitions name

(* Handle scoping effects *)
module Handler = struct
  let pp_path fmt = function
    | Emp -> Format.pp_print_string fmt "(root)"
    | path -> Format.pp_print_string fmt @@ String.concat "." (Bwd.to_list path)
  ;;

  let pp_context fmt = function
    | Some `Visible -> Format.pp_print_string fmt " in the visible namespace"
    | Some `Export -> Format.pp_print_string fmt " in the export namespace"
    | None -> ()
  ;;

  let pp_item fmt = function
    | x, `Imported -> Format.fprintf fmt "%s (imported)" ([%show: Core.value] x)
    | x, `Constructor -> Format.fprintf fmt "%s (constructor)" ([%show: Core.value] x)
  ;;

  let shadow context path x y =
    Reporter.tracef
      "shadowing, env, %a := %a ~> env, %a := %a%a.@."
      pp_path
      path
      pp_item
      x
      pp_path
      path
      pp_item
      y
      pp_context
      context
    @@ fun () -> y
  ;;

  let not_found context prefix =
    Eio.traceln
      "[Warning] Could not find any data within the subtree at %a%a.@."
      pp_path
      prefix
      pp_context
      context
  ;;

  let hook context prefix hook input =
    match hook with
    | Trace ->
      Eio.traceln
        "@[<v 2>[Info] Got the following bindings at %a%a:@;"
        pp_path
        prefix
        pp_context
        context;
      Trie.iter (fun path x -> Eio.traceln "%a => %a@;" pp_path path pp_item x) input;
      Eio.traceln "@]@.";
      input
  ;;
end
