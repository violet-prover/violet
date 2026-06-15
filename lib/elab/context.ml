open Yuujinchou
open Bwd
open Violet_surface
open Violet_common
module Syntax = Violet_kernel.Syntax
module Context_view = Violet_kernel.Context_view
module Pretty = Violet_kernel.Pretty
open Syntax

type binder_kind =
  | Regular
  | Recursive of string list

type ctor_info =
  { ctor_name : string
  ; binder_names : string list
  ; binder_kinds : binder_kind list
  }

type polarity =
  | StrictlyPositive
  | Unrestricted
[@@deriving show]

type ind_info =
  { params : Surface.pretype Surface.sbinder list
  ; deps : Surface.pretype Surface.sbinder list
  ; ind_ty : Surface.pretype
  ; ctors : Surface.pretype Surface.sbinder list
  ; infos : ctor_info list
  ; param_polarity : polarity list
  }

type modifier_cmd = Trace

module TypeContext = struct
  type data = Core.value_ty

  (* Locals are handled in Elab's local_ctx with de Bruijn indices.
     Only globals remain here. *)
  type tag =
    [ `Imported
    | `Defn
    | `Constructor
    | `Eliminator
    | `Inductive of ind_info
    ]

  type hook = modifier_cmd

  type context =
    [ `Visible
    | `Export
    ]
end

module S = Scope.Make (TypeContext)

let has (x : string) : bool =
  match S.resolve [ x ] with
  | Some _ -> true
  | _ -> false
;;

(* When a bare name fails to resolve it may still be a data constructor:
   constructors live in the scope at [ind; ctor], never at bare [ctor], and
   are only resolved type-directed in checking position (see Elab's
   `GCheck (loc, Var [x], expected)` case, which forces `expected` to an
   `IndType` to find `ind/x`). In an inferred position — e.g. as a function
   head — that path can't run, so the bare name is genuinely unbound. Collect
   the inductives declaring a constructor named [x] so `lookup` can say so. *)
let constructor_owners (x : string) : string list =
  let owners = ref [] in
  Trie.iter
    (fun path (_, tag) ->
       match tag with
       | `Constructor ->
         (match List.rev (Bwd.to_list path) with
          | ctor :: ind :: _ when String.equal ctor x ->
            if not (List.mem ind !owners) then owners := ind :: !owners
          | _ -> ())
       | _ -> ())
    (S.get_visible ());
  List.rev !owners
;;

let lookup (x : string) : Core.value_ty =
  match S.resolve [ x ] with
  | Some (v, _) -> v
  | None ->
    (match constructor_owners x with
     | [] -> Reporter.fatalf NoVar_error "`%s` is not defined" x
     | owners ->
       Reporter.fatalf
         NoVar_error
         "`%s` is a constructor of `%s`; it can only be used where its expected type is \
          known (e.g. checked against `%s …`), not as a function head or in an inferred \
          position"
         x
         (String.concat "`, `" owners)
         (List.hd owners))
;;

let lookup_path (xs : Trie.path) : Core.value_ty =
  match S.resolve xs with
  | Some (v, _) -> v
  | None -> Reporter.fatalf NoVar_error "`%s` is not defined" (Syntax.Name.of_segments xs)
;;

let has_path (xs : Trie.path) : bool = Option.is_some (S.resolve xs)

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
    | `Inductive _ -> Format.fprintf fmt "%s (inductive)" s
  ;;

  let shadow context path x y =
    Reporter.tracef
      "shadowing, Γ, %a : %a ~> Γ, %a : %a%a.@."
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

(* Level variables declared by `\universe U V` in the current module's scope.
   Reset per module (see Elab.check_module). *)
let level_vars : (string, unit) Hashtbl.t = Hashtbl.create ~random:true 16
let declare_level_var (name : string) : unit = Hashtbl.replace level_vars name ()
let is_level_var (name : string) : bool = Hashtbl.mem level_vars name
let clear_level_vars () : unit = Hashtbl.clear level_vars

let declared_level_vars () : string list =
  Hashtbl.fold (fun k () acc -> k :: acc) level_vars []
;;

let%expect_test "declare and lookup level var" =
  clear_level_vars ();
  declare_level_var "U";
  print_string @@ string_of_bool (is_level_var "U");
  print_newline ();
  print_string @@ string_of_bool (is_level_var "V");
  [%expect
    {|
    true
    false |}]
;;
