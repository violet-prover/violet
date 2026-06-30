open Yuujinchou
open Bwd
open Violet_common
module Syntax = Violet_kernel.Syntax
module Context_view = Violet_kernel.Context_view
module Pretty = Violet_kernel.Pretty
open Syntax

type modifier_cmd = Trace

module ValueEnvironment = struct
  type data = Core.value

  (* Locals are handled in Elab's local_ctx with de Bruijn indices.
     Only globals remain here. *)
  type tag =
    [ `Imported
    | `Defn
    | `Constructor
    | `Eliminator
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
      (Syntax.Name.of_segments [ x ])
;;

let lookup_path (xs : Trie.path) : Core.value =
  match S.resolve xs with
  | Some (v, _) -> v
  | None ->
    Reporter.fatalf
      NoVar_error
      "cannot find `%s` in environment"
      (Syntax.Name.of_segments xs)
;;

(* Top-level let definitions, keyed by name.  Unification consults this when
   it needs to unfold a `Var (x, _)` opaque head.  Constructors and inductive
   types live in Yuujinchou (S) only — they're not "defined" in the same sense. *)
let definitions : (string, Core.value) Hashtbl.t = Hashtbl.create ~random:true 100

let register_definition (name : string) (v : Core.value) : unit =
  Hashtbl.replace definitions name v
;;

let unfold_def (name : string) : Core.value option = Hashtbl.find_opt definitions name

module Handler = struct
  let pp_path fmt = function
    | Emp -> Format.pp_print_string fmt "(root)"
    | path -> Format.pp_print_string fmt @@ Syntax.Name.of_segments (Bwd.to_list path)
  ;;

  let pp_context fmt = function
    | Some `Visible -> Format.pp_print_string fmt " in the visible namespace"
    | Some `Export -> Format.pp_print_string fmt " in the export namespace"
    | None -> ()
  ;;

  let pp_item fmt (x, tag) =
    let s = Notation.pp_value Context_view.empty x in
    match tag with
    | `Imported -> Format.fprintf fmt "%s (imported)" s
    | `Defn -> Format.fprintf fmt "%s (defn)" s
    | `Constructor -> Format.fprintf fmt "%s (constructor)" s
    | `Eliminator -> Format.fprintf fmt "%s (eliminator)" s
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

let lookup_or_var (x : string) : Core.value =
  match S.resolve [ x ] with
  | Some (v, _) -> v
  | None -> Core.var_ x
;;

module View : Violet_kernel.Views.ENV_VIEW = struct
  let lookup = lookup_or_var
  let unfold = unfold_def
end
