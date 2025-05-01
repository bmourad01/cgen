(* Checking type definitions. *)

open Core
open Virtual
open Typecheck_common

let add m =
  let* init = getenv in
  let* env = Module.typs m |> M.Seq.fold ~init ~f:(fun env t ->
      M.lift_err @@ Env.add_typ t env) in
  updenv env

let check =
  let* env = getenv in
  Type.layouts_of_types (Map.data env.tenv) >>?
  M.List.fold ~init:env ~f:(fun env (name, l) ->
      match Map.add env.genv ~key:name ~data:l with
      | `Ok genv -> !!{env with genv}
      | `Duplicate ->
        M.failf "Redefinition of layout for :%s"
          name ()) >>= updenv
