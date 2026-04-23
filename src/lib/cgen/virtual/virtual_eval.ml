open Core

module Insn = Virtual_insn

let int8  i = Bv.(int   i mod Bv.m8)
let int16 i = Bv.(int   i mod Bv.m16)
let int32 i = Bv.(int32 i mod Bv.m32)
let int64 i = Bv.(int64 i mod Bv.m64)

external float_unordered :
  float -> float -> bool = "cgen_float_is_unordered" [@@noalloc]

external float_ordered :
  float -> float -> bool = "cgen_float_is_ordered" [@@noalloc]

external float_to_bits   : float -> int64 = "cgen_bits_of_float"
external float_of_bits   : int64 -> float = "cgen_float_of_bits"
external float_to_int8   : float -> int   = "cgen_int8_of_float" [@@noalloc]
external float_to_int16  : float -> int   = "cgen_int16_of_float" [@@noalloc]
external float_to_int32  : float -> int32 = "cgen_int32_of_float"
external float_to_int64  : float -> int64 = "cgen_int64_of_float"
external float_to_uint8  : float -> int   = "cgen_uint8_of_float" [@@noalloc]
external float_to_uint16 : float -> int   = "cgen_uint16_of_float" [@@noalloc]
external float_to_uint32 : float -> int32 = "cgen_uint32_of_float"
external float_to_uint64 : float -> int64 = "cgen_uint64_of_float"
external float_of_int8   : int   -> float = "cgen_float_of_int8"
external float_of_int16  : int   -> float = "cgen_float_of_int16"
external float_of_int32  : int32 -> float = "cgen_float_of_int32"
external float_of_int64  : int64 -> float = "cgen_float_of_int64"
external float_of_uint8  : int   -> float = "cgen_float_of_uint8"
external float_of_uint16 : int   -> float = "cgen_float_of_uint16"
external float_of_uint32 : int32 -> float = "cgen_float_of_uint32"
external float_of_uint64 : int64 -> float = "cgen_float_of_uint64"

(* pre: x is nonzero *)
let clz x n =
  let i = Bv.clz x n in
  Bv.(int i mod modulus n)

(* pre: x is nonzero *)
let ctz x n =
  let i = Bv.ctz x n in
  Bv.(int i mod modulus n)

let popcnt x n =
  let i = Bv.popcnt x in
  Bv.(int i mod modulus n)

let immsz t = Type.sizeof_imm t
let imod t = Bv.modulus @@ immsz t

let umulh t a b =
  let sz = immsz t in
  let m = Bv.modulus sz in
  let m2 = Bv.modulus (sz * 2) in
  let sh = Bv.(int sz mod m) in
  Bv.((((a * b) mod m2) lsr sh) mod m)

let mulh t a b =
  let c = umulh t a b in
  let m = imod t in
  let s1 = if Bv.(msb a mod m) then b else Bv.zero in
  let s2 = if Bv.(msb b mod m) then a else Bv.zero in
  Bv.((((c - s1) mod m) - s2) mod m)

let rol t a b =
  let sz = immsz t in
  let m = Bv.modulus sz in
  let sh = Bv.(((int sz mod m) - b) mod m) in
  let lsh = Bv.((a lsl b) mod m) in
  let rsh = Bv.((a lsr sh) mod m) in
  Bv.((lsh lor rsh) mod m)

let ror t a b =
  let sz = immsz t in
  let m = Bv.modulus sz in
  let sh = Bv.(((int sz mod m) - b) mod m) in
  let lsh = Bv.((a lsl sh) mod m) in
  let rsh = Bv.((a lsr b) mod m) in
  Bv.((lsh lor rsh) mod m)

let sext t a ta =
  let sz' = immsz ta in
  let m' = Bv.modulus sz' in
  if Bv.(msb a mod m') then
    let m = imod t in
    let sh = Bv.(int sz' mod m) in
    Bv.(((((ones mod m) lsl sh) mod m) lor a) mod m)
  else a

let shift_fits t s =
  let sz = immsz t in
  let m = Bv.modulus sz in
  Bv.(s < int sz mod m)

let binop_int o a b = match (o : Insn.binop) with
  | `add (#Type.imm as t) -> Some (`int (Bv.((a + b) mod imod t), t))
  | `div (#Type.imm as t) when Bv.(b <> zero) ->
    Some (`int (Bv.((sdiv a b) mod imod t), t))
  | `mul (#Type.imm as t) -> Some (`int (Bv.((a * b) mod imod t), t))
  | `mulh (#Type.imm as t) -> Some (`int (mulh t a b, t))
  | `umulh (#Type.imm as t) -> Some (`int (umulh t a b, t))
  | `rem t when Bv.(b <> zero) ->
    Some (`int (Bv.(srem' a b (immsz t)), t))
  | `sub (#Type.imm as t) -> Some (`int (Bv.((a - b) mod imod t), t))
  | `udiv t when Bv.(b <> zero) ->
    Some (`int (Bv.((a / b) mod imod t), t))
  | `urem t when Bv.(b <> zero) ->
    Some (`int (Bv.((rem a b) mod imod t), t))
  | `and_ t -> Some (`int (Bv.((a land b) mod imod t), t))
  | `or_  t -> Some (`int (Bv.((a lor  b) mod imod t), t))
  | `asr_ t when shift_fits t b -> Some (`int (Bv.((a asr  b) mod imod t), t))
  | `lsl_ t when shift_fits t b -> Some (`int (Bv.((a lsl  b) mod imod t), t))
  | `lsr_ t when shift_fits t b -> Some (`int (Bv.((a lsr  b) mod imod t), t))
  | `rol t  when shift_fits t b -> Some (`int (rol t a b, t))
  | `ror t  when shift_fits t b -> Some (`int (ror t a b, t))
  | `xor t  -> Some (`int (Bv.((a lxor b) mod imod t), t))
  | `eq #Type.imm -> Some (`bool Bv.(a =  b))
  | `ge #Type.imm -> Some (`bool Bv.(a >= b))
  | `gt #Type.imm -> Some (`bool Bv.(a >  b))
  | `le #Type.imm -> Some (`bool Bv.(a <= b))
  | `lt #Type.imm -> Some (`bool Bv.(a <  b))
  | `ne #Type.imm -> Some (`bool Bv.(a <> b))
  | `sge t -> Some (`bool (Bv.signed_compare a b (immsz t) >= 0))
  | `sgt t -> Some (`bool (Bv.signed_compare a b (immsz t) >  0))
  | `sle t -> Some (`bool (Bv.signed_compare a b (immsz t) <= 0))
  | `slt t -> Some (`bool (Bv.signed_compare a b (immsz t) <  0))
  | _ -> None

(* NaN will compare not equal, not greater than, and not less than
   every value, including itself. *)
let cmp_nan k n a b = not (n a) && not (n b) && k a b

let binop_single o a b =
  let open Float32 in
  match (o : Insn.binop) with
  | `add `f32 -> Some (`float (a + b))
  | `div `f32 -> Some (`float (a / b))
  | `mul `f32 -> Some (`float (a * b))
  | `sub `f32 -> Some (`float (a - b))
  | `eq  `f32 -> Some (`bool (cmp_nan (=)  is_nan a b))
  | `ge  `f32 -> Some (`bool (cmp_nan (>=) is_nan a b))
  | `gt  `f32 -> Some (`bool (cmp_nan (>)  is_nan a b))
  | `le  `f32 -> Some (`bool (cmp_nan (<=) is_nan a b))
  | `lt  `f32 -> Some (`bool (cmp_nan (<)  is_nan a b))
  | `ne  `f32 -> Some (`bool (not @@ cmp_nan (=) is_nan a b))
  | `o   `f32 -> Some (`bool (is_ordered a b))
  | `uo  `f32 -> Some (`bool (is_unordered a b))
  | _ -> None

let binop_double o a b =
  let open Float in
  match (o : Insn.binop) with
  | `add `f64 -> Some (`double (a + b))
  | `div `f64 -> Some (`double (a / b))
  | `mul `f64 -> Some (`double (a * b))
  | `sub `f64 -> Some (`double (a - b))
  | `eq  `f64 -> Some (`bool (cmp_nan (=)  is_nan a b))
  | `ge  `f64 -> Some (`bool (cmp_nan (>=) is_nan a b))
  | `gt  `f64 -> Some (`bool (cmp_nan (>)  is_nan a b))
  | `le  `f64 -> Some (`bool (cmp_nan (<=) is_nan a b))
  | `lt  `f64 -> Some (`bool (cmp_nan (<)  is_nan a b))
  | `ne  `f64 -> Some (`bool (not @@ cmp_nan (=) is_nan a b))
  | `o   `f64 -> Some (`bool (float_ordered a b))
  | `uo  `f64 -> Some (`bool (float_unordered a b))
  | _ -> None

let unop_int o a ty = match (o : Insn.unop) with
  | `neg (#Type.imm as t) ->
    Some (`int (Bv.(neg a mod imod t), t))
  | `clz t when Bv.(a <> zero) ->
    Some (`int (clz a @@ immsz t, t))
  | `ctz t when Bv.(a <> zero) ->
    Some (`int (ctz a @@ immsz t, t))
  | `not_ t ->
    Some (`int (Bv.(lnot a mod imod t), t))
  | `popcnt t ->
    Some (`int (popcnt a @@ immsz t, t))
  | `fibits `f32 ->
    Some (`float (Float32.of_bits @@ Bv.to_int32 a))
  | `fibits `f64 ->
    Some (`double (float_of_bits @@ Bv.to_int64 a))
  | `itrunc t when Type.equal_imm t ty -> Some (`int (a, t))
  | `itrunc t ->
    let hi = immsz t - 1 in
    Some (`int (Bv.extract ~hi ~lo:0 a, t))
  | `sext t when Type.equal_imm t ty -> Some (`int (a, t))
  | `sext t -> Some (`int (sext t a ty, t))
  | `sitof (`i8,  `f32) -> Some (`float  (Float32.of_int8   @@ Bv.to_int   a))
  | `sitof (`i16, `f32) -> Some (`float  (Float32.of_int16  @@ Bv.to_int   a))
  | `sitof (`i32, `f32) -> Some (`float  (Float32.of_int32  @@ Bv.to_int32 a))
  | `sitof (`i64, `f32) -> Some (`float  (Float32.of_int64  @@ Bv.to_int64 a))
  | `sitof (`i8,  `f64) -> Some (`double (float_of_int8     @@ Bv.to_int   a))
  | `sitof (`i16, `f64) -> Some (`double (float_of_int16    @@ Bv.to_int   a))
  | `sitof (`i32, `f64) -> Some (`double (float_of_int32    @@ Bv.to_int32 a))
  | `sitof (`i64, `f64) -> Some (`double (float_of_int64    @@ Bv.to_int64 a))
  | `uitof (`i8,  `f32) -> Some (`float  (Float32.of_uint8  @@ Bv.to_int   a))
  | `uitof (`i16, `f32) -> Some (`float  (Float32.of_uint16 @@ Bv.to_int   a))
  | `uitof (`i32, `f32) -> Some (`float  (Float32.of_uint32 @@ Bv.to_int32 a))
  | `uitof (`i64, `f32) -> Some (`float  (Float32.of_uint64 @@ Bv.to_int64 a))
  | `uitof (`i8,  `f64) -> Some (`double (float_of_uint8    @@ Bv.to_int   a))
  | `uitof (`i16, `f64) -> Some (`double (float_of_uint16   @@ Bv.to_int   a))
  | `uitof (`i32, `f64) -> Some (`double (float_of_uint32   @@ Bv.to_int32 a))
  | `uitof (`i64, `f64) -> Some (`double (float_of_uint64   @@ Bv.to_int64 a))
  | `zext t -> Some (`int (a, t))
  | `copy (#Type.imm as t) -> Some (`int (a, t))
  | _ -> None

let unop_single o a = match (o : Insn.unop) with
  | `neg  `f32 -> Some (`float (Float32.neg a))
  | `fext `f64 -> Some (`double (Float32.to_float a))
  | `fext `f32 | `ftrunc `f32 | `copy `f32 -> Some (`float a)
  | `ftosi (`f32, `i8) ->
    Some (`int (int8  @@ Float32.to_int8   a, `i8))
  | `ftosi (`f32, `i16) ->
    Some (`int (int16 @@ Float32.to_int16  a, `i16))
  | `ftosi (`f32, `i32) ->
    Some (`int (int32 @@ Float32.to_int32  a, `i32))
  | `ftosi (`f32, `i64) ->
    Some (`int (int64 @@ Float32.to_int64  a, `i64))
  | `ftoui (`f32, `i8) ->
    Some (`int (int8  @@ Float32.to_uint8  a, `i8))
  | `ftoui (`f32, `i16) ->
    Some (`int (int16 @@ Float32.to_uint16 a, `i16))
  | `ftoui (`f32, `i32) ->
    Some (`int (int32 @@ Float32.to_uint32 a, `i32))
  | `ftoui (`f32, `i64) ->
    Some (`int (int64 @@ Float32.to_uint64 a, `i64))
  | `ifbits t ->
    let t = (t :> Type.imm) in
    Some (`int (Bv.(int32 (Float32.bits a) mod imod t), t))
  | _ -> None

let unop_double o a = match (o : Insn.unop) with
  | `neg  `f64 -> Some (`double (Float.neg a))
  | `fext `f64 | `ftrunc `f64 | `copy `f64 -> Some (`double a)
  | `ftosi (`f64, `i8) ->
    Some (`int (int8  @@ float_to_int8   a, `i8))
  | `ftosi (`f64, `i16) ->
    Some (`int (int16 @@ float_to_int16  a, `i16))
  | `ftosi (`f64, `i32) ->
    Some (`int (int32 @@ float_to_int32  a, `i32))
  | `ftosi (`f64, `i64) ->
    Some (`int (int64 @@ float_to_int64  a, `i64))
  | `ftoui (`f64, `i8) ->
    Some (`int (int8  @@ float_to_uint8  a, `i8))
  | `ftoui (`f64, `i16) ->
    Some (`int (int16 @@ float_to_uint16 a, `i16))
  | `ftoui (`f64, `i32) ->
    Some (`int (int32 @@ float_to_uint32 a, `i32))
  | `ftoui (`f64, `i64) ->
    Some (`int (int64 @@ float_to_uint64 a, `i64))
  | `ifbits t ->
    let t = (t :> Type.imm) in
    Some (`int (Bv.(int64 (float_to_bits a) mod imod t), t))
  | _ -> None
