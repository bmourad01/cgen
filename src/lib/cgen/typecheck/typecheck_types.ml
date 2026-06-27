(* Checking type definitions. *)

open Core
open Virtual
open Typecheck_common

let add m =
  let* init = getenv in
  let* env = Module.typs m |> M.Seq.fold ~init ~f:(fun env t ->
      M.lift_err @@ Env.add_typ t env) in
  updenv env
