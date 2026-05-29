open Violet_surface
module Check = Wiring.Check

let report_rejection ~loc ~name err =
  match err with
  | Violet_kernel.Error.OrphanMeta mv ->
    (match Meta.origin_of mv with
     | Some { loc; display } ->
       Reporter.fatalf ~loc Elab_error "cannot infer implicit %s" display
     | None ->
       Reporter.fatalf
         ~loc
         Elab_error
         "kernel rejected `%s`: %s"
         name
         (Violet_kernel.Error.show_kernel_error err))
  | _ ->
    Reporter.fatalf
      ~loc
      Elab_error
      "kernel rejected `%s`: %s"
      name
      (Violet_kernel.Error.show_kernel_error err)
;;

let accept_let m ~loc ~name ~ty ~body =
  try Check.accept_let m ~name ~ty ~body with
  | Violet_kernel.Error.Kernel_error err -> report_rejection ~loc ~name err
;;

let accept_data m ~loc ~name ~ty ~ctor_names =
  try Check.accept_data m ~name ~ty ~ctor_names with
  | Violet_kernel.Error.Kernel_error err -> report_rejection ~loc ~name err
;;

let accept_ctor m ~loc ~name ~data ~ty =
  try Check.accept_ctor m ~name ~data ~ty with
  | Violet_kernel.Error.Kernel_error err -> report_rejection ~loc ~name err
;;

let accept_elim m ~loc ~name ~ty ~reducer =
  try Check.accept_elim m ~name ~ty ~reducer with
  | Violet_kernel.Error.Kernel_error err -> report_rejection ~loc ~name err
;;
