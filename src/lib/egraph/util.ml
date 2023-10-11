open Core
open Monads.Std

external float_of_bits : int64 -> float = "cgen_float_of_bits"
external float_to_bits : float -> int64 = "cgen_bits_of_float"

let single_val v ty : Virtual.const option = match ty with
  | #Type.imm as t -> Some (`int (v, t))
  | `f32 -> Some (`float (Float32.of_bits @@ Bv.to_int32 v))
  | `f64 -> Some (`double (float_of_bits @@ Bv.to_int64 v))
  | `flag -> Some (`bool Bv.(v <> zero))
  | _ -> None

module I = Bv_interval

open Monad.Option.Let

let single_interval iv ty : Virtual.const option =
  let* iv = iv and* ty = ty in
  let* v = I.single_of iv in
  single_val v ty

let interval_of_const ~wordsz : Virtual.const -> Bv_interval.t = function
  | `bool b -> I.boolean b
  | `int (value, t) ->
    I.create_single ~value ~size:(Type.sizeof_imm t)
  | `float f ->
    let value = Bv.M32.int32 @@ Float32.bits f in
    I.create_single ~value ~size:32
  | `double d ->
    let value = Bv.M64.int64 @@ float_to_bits d in
    I.create_single ~value ~size:64
  | `sym _ -> I.create_full ~size:wordsz
