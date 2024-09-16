open Yuujinchou
open Bwd
open Syntax

type modifier_cmd = Trace

module TypeContext = struct
  type data = Core.value_ty
  type tag = [ `Imported | `Local | `Constructor ]
  type hook = modifier_cmd
  type context = [ `Visible | `Export ]
end

module S = Scope.Make (TypeContext)

let lookup (x : string) : Core.value_ty =
  match S.resolve [ x ] with
  | Some (v, _) -> v
  | None ->
      Reporter.fatalf NoVar_error "cannot find type of `%s` in context"
        (String.concat " " [ x ])

(* Handle scoping effects *)
module Handler = struct
  let pp_path fmt = function
    | Emp -> Format.pp_print_string fmt "(root)"
    | path -> Format.pp_print_string fmt @@ String.concat "." (Bwd.to_list path)

  let pp_context fmt = function
    | Some `Visible -> Format.pp_print_string fmt " in the visible namespace"
    | Some `Export -> Format.pp_print_string fmt " in the export namespace"
    | None -> ()

  let pp_item fmt = function
    | x, `Imported ->
        Format.fprintf fmt "%s (imported)" ([%show: Core.value_ty] x)
    | x, `Local -> Format.fprintf fmt "%s (local)" ([%show: Core.value_ty] x)
    | x, `Constructor ->
        Format.fprintf fmt "%s (constructor)" ([%show: Core.value_ty] x)

  let shadow context path x y =
    Eio.traceln "shadowing, Γ, %a : %a ~> Γ, %a : %a%a.@."
      pp_path path
      pp_item x
      pp_path path
      pp_item y
      pp_context context;
    y

  let not_found context prefix =
    Eio.traceln
      "[Warning] Could not find any data within the subtree at %a%a.@." pp_path
      prefix pp_context context

  let hook context prefix hook input =
    match hook with
    | Trace ->
        Eio.traceln "@[<v 2>[Info] Got the following bindings at %a%a:@;"
          pp_path prefix pp_context context;
        Trie.iter
          (fun path x -> Eio.traceln "%a => %a@;" pp_path path pp_item x)
          input;
        Eio.traceln "@]@.";
        input
end
