(* Checking global data. *)

open Core
open Virtual
open Typecheck_common

let invalid_elt d elt msg =
  M.failf "Invalid element %a ia data $%s: %s"
    Data.pp_elt elt (Data.name d) msg ()

let add m =
  let* init = getenv in
  let* env = Module.data m |> M.Seq.fold ~init ~f:(fun env d ->
      M.lift_err @@ Env.add_data d env) in
  updenv env

let check_align d = match Data.align d with
  | Some n when n <= 0 || n land (n - 1) <> 0 ->
    M.failf "Invalid alignment %d of data $%s: must \
             be a positive power of two"
      n (Data.name d) ()
  | Some _ | None -> !!()

let check_elts d = Data.elts d |> M.Seq.iter ~f:(function
    | #const | `string _ -> !!()
    | `zero n when n >= 1 -> !!()
    | `zero _ as elt ->
      invalid_elt d (elt :> Data.elt)
        "argument must be greater than 0")

let check d =
  let* () = check_align d in
  let* () = check_elts d in
  !!()
