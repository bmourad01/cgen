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

let infer_ty_binop : Virtual.Insn.binop -> Type.t option = function
  | `add t
  | `div t
  | `mul t
  | `rem t
  | `sub t -> Some (t :> Type.t)
  | `mulh t
  | `udiv t
  | `umulh t
  | `urem t
  | `and_ t
  | `or_ t
  | `asr_ t
  | `lsl_ t
  | `lsr_ t
  | `rol t
  | `ror t
  | `xor t -> Some (t :> Type.t)
  | #Virtual.Insn.cmp -> Some `flag

let infer_ty_unop ~tty ~word : Virtual.Insn.unop -> Type.t option = function
  | `neg t
  | `copy t -> Some (t :> Type.t)
  | `ref -> Some word
  | `clz t
  | `ctz t
  | `not_ t
  | `popcnt t
  | `flag t
  | `ftosi (_, t)
  | `ftoui (_, t)
  | `itrunc t
  | `sext t
  | `zext t -> Some (t :> Type.t)
  | `ifbits t -> Some (t :> Type.t)
  | `fext t
  | `fibits t
  | `ftrunc t
  | `sitof (_, t)
  | `uitof (_, t) -> Some (t :> Type.t)
  | `unref n -> tty n

let infer_ty ~tid ~tty ~tvar ~word : Enode.t -> Type.t option = function
  | U {pre; post} ->
    let tpre = tid pre in
    let tpost = tid post in
    Option.merge tpre tpost ~f:(fun x y ->
        assert (Type.equal x y);
        x)
  | N (o, _) -> match o with
    | Oaddr _ -> Some word
    | Obinop b -> infer_ty_binop b
    | Obool _ -> Some `flag
    | Obr -> None
    | Ocall0 _ -> None
    | Ocall (_, t) -> Some (t :> Type.t)
    | Ocallargs -> None
    | Odouble _ -> Some `f64
    | Ojmp -> None
    | Oint (_, t) -> Some (t :> Type.t)
    | Oload (_, t) -> Some (t :> Type.t)
    | Olocal _ -> None
    | Oret -> None
    | Osel t -> Some (t :> Type.t)
    | Oset _ -> None
    | Osingle _ -> Some `f32
    | Ostore _ -> None
    | Osw _ -> None
    | Osym _ -> Some word
    | Otbl _ -> None
    | Otcall0 -> None
    | Otcall _ -> None
    | Ounop u -> infer_ty_unop ~tty ~word u
    | Ovaarg (_, t) -> Some (t :> Type.t)
    | Ovar x -> tvar x
    | Ovastart _ -> None
