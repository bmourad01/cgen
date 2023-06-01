open Core
open Virtual
open Common

module Util = struct
  let int8  i = Bitvec.(int   i mod Bitvec.m8)
  let int16 i = Bitvec.(int   i mod Bitvec.m16)
  let int32 i = Bitvec.(int32 i mod Bitvec.m32)
  let int64 i = Bitvec.(int64 i mod Bitvec.m64)

  external float_unordered :
    float -> float -> bool = "cgen_float_is_unordered" [@@noalloc]

  external float_ordered :
    float -> float -> bool = "cgen_float_is_ordered" [@@noalloc]

  external float_to_bits : float -> int64 = "cgen_bits_of_float"
  external float_of_bits : int64 -> float = "cgen_float_of_bits"

  external float_to_int8   : float     -> int   = "cgen_int8_of_float" [@@noalloc]
  external float_to_int16  : float     -> int   = "cgen_int16_of_float" [@@noalloc]
  external float_to_int32  : float     -> int32 = "cgen_int32_of_float"
  external float_to_int64  : float     -> int64 = "cgen_int64_of_float"
  external float_to_uint8  : float     -> int   = "cgen_uint8_of_float" [@@noalloc]
  external float_to_uint16 : float     -> int   = "cgen_uint16_of_float" [@@noalloc]
  external float_to_uint32 : float     -> int32 = "cgen_uint32_of_float"
  external float_to_uint64 : float     -> int64 = "cgen_uint64_of_float"
  external float_of_int8   : int   -> float     = "cgen_float_of_int8"
  external float_of_int16  : int   -> float     = "cgen_float_of_int16"
  external float_of_int32  : int32 -> float     = "cgen_float_of_int32"
  external float_of_int64  : int64 -> float     = "cgen_float_of_int64"
  external float_of_uint8  : int   -> float     = "cgen_float_of_uint8"
  external float_of_uint16 : int   -> float     = "cgen_float_of_uint16"
  external float_of_uint32 : int32 -> float     = "cgen_float_of_uint32"
  external float_of_uint64 : int64 -> float     = "cgen_float_of_uint64"

  let signed_compare x y m = match Bitvec.(msb x mod m, msb y mod m) with
    | true,  true  -> Bitvec.compare y x
    | false, false -> Bitvec.compare x y
    | true,  false -> -1
    | false, true  -> 1

  (* pre: x is nonzero *)
  let clz x n =
    let i = Bitvec.to_int64 x in
    let i = match n with
      | (8|16|32|64) -> Int64.(clz (i lsl Int.(64 - n)))
      | _ -> assert false in
    Bitvec.(int i mod modulus n)

  (* pre: x is nonzero *)
  let ctz x n =
    let i = Bitvec.to_int64 x in
    let i = match n with
      | (8|16|32|64) -> Int64.ctz i
      | _ -> assert false in
    Bitvec.(int i mod modulus n)

  let popcnt x n =
    let x = Bitvec.to_bigint x in
    Bitvec.(int (Z.popcount x) mod modulus n)
end

let rec eval_pure ?(env = Var.Map.empty) e =
  let pure = eval_pure ~env in
  let imod t = Bitvec.modulus @@ Type.sizeof_imm t in
  match e with
  | Palloc _ as a -> a
  | Pbinop (l, o, a, b) ->
    begin match o, pure a, pure b with
      (* ADD *)
      | `add (#Type.imm as t), Pint (a, _), Pint (b, _) ->
        Pint (Bitvec.((a + b) mod imod t), t)
      | `add #Type.imm, a, Pint (b, _) when Bitvec.(b = zero) -> a
      | `add #Type.imm, Pint (a, _), b when Bitvec.(a = zero) -> b
      | `add `f32, Psingle a, Psingle b ->
        Psingle Float32.(a + b)
      | `add `f64, Pdouble a, Pdouble b ->
        Pdouble Float.(a + b)
      (* DIV *)
      | `div #Type.imm, a, Pint (b, _) when Bitvec.(b = one) -> a
      | `div (#Type.imm as t), Pint (a, _), Pint (b, _)
        when Bitvec.(b <> zero) ->
        Pint (Bitvec.((sdiv a b) mod imod t), t)
      | `div `f32, Psingle a, Psingle b ->
        Psingle Float32.(a / b)
      | `div `f64, Pdouble a, Pdouble b ->
        Pdouble Float.(a / b)
      (* MUL *)
      | `mul (#Type.imm as t), _, Pint (z, _) when Bitvec.(z = zero) ->
        Pint (z, t)
      | `mul (#Type.imm as t), Pint (z, _), _ when Bitvec.(z = zero) ->
        Pint (z, t)
      | `mul #Type.imm, a, Pint (b, _) when Bitvec.(b = one) -> a
      | `mul #Type.imm, Pint (a, _), b when Bitvec.(a = one) -> b
      | `mul (#Type.imm as t), Pint (a, _), Pint (b, _) ->
        Pint (Bitvec.((a * b) mod imod t), t)
      | `mul `f32, Psingle a, Psingle b ->
        Psingle Float32.(a * b)
      | `mul `f64, Pdouble a, Pdouble b ->
        Pdouble Float.(a * b)
      (* MULH *)
      | `mulh (#Type.imm as t), _, Pint (z, _) when Bitvec.(z = zero) ->
        Pint (z, t)
      | `mulh (#Type.imm as t), Pint (z, _), _ when Bitvec.(z = zero) ->
        Pint (z, t)
      | `mulh #Type.imm, a, Pint (b, _) when Bitvec.(b = one) -> a
      | `mulh #Type.imm, Pint (a, _), b when Bitvec.(a = one) -> b
      | `mulh t, Pint (a, _), Pint (b, _) ->
        let sz = Type.sizeof_imm t in
        let m = Bitvec.modulus sz in
        let m2 = Bitvec.modulus (sz * 2) in
        let sh = Bitvec.(int sz mod m) in
        Pint (Bitvec.((((a * b) mod m2) lsr sh) mod m), t)
      (* REM *)
      | `rem (#Type.imm as t), _, Pint (b, _) when Bitvec.(b = one) ->
        Pint (Bitvec.zero, t)
      | `rem (#Type.imm as t), Pint (a, _), Pint (b, _)
        when Bitvec.(b <> zero) ->
        Pint (Bitvec.((srem a b) mod imod t), t)
      | `rem `f32, Psingle a, Psingle b ->
        Psingle Float32.(rem a b)
      | `rem `f64, Pdouble a, Pdouble b ->
        Pdouble Float.(a % b)
      (* SUB *)
      | `sub #Type.imm, a, Pint (b, _) when Bitvec.(b = zero) -> a
      | `sub (#Type.imm as t), Pint (a, _), Pint (b, _) ->
        Pint (Bitvec.((a - b) mod imod t), t)
      | `sub `f32, Psingle a, Psingle b ->
        Psingle Float32.(a - b)
      | `sub `f64, Pdouble a, Pdouble b ->
        Pdouble Float.(a - b)
      (* UDIV *)
      | `udiv _, a, Pint (b, _) when Bitvec.(b = one) -> a
      | `udiv t, Pint (a, _), Pint (b, _) when Bitvec.(b <> zero) ->
        Pint (Bitvec.((div a b) mod imod t), t)
      (* UREM *)
      | `urem t, _, Pint (b, _) when Bitvec.(b = one) ->
        Pint (Bitvec.zero, t)
      | `urem t, Pint (a, _), Pint (b, _) when Bitvec.(b <> zero) ->
        Pint (Bitvec.((rem a b) mod imod t), t)
      (* AND *)
      | `and_ t, _, Pint (z, _) when Bitvec.(z = zero) ->
        Pint (z, t)
      | `and_ t, Pint (z, _), _ when Bitvec.(z = zero) ->
        Pint (z, t)
      | `and_ t, a, Pint (b, _) when Bitvec.(b = ones mod imod t) -> a
      | `and_ t, Pint (a, _), b when Bitvec.(a = ones mod imod t) -> b
      | `and_ t, Pint (a, _), Pint (b, _) ->
        Pint (Bitvec.((a land b) mod imod t), t)
      | `and_ _, Pvar a, Pvar b when Var.(a = b) -> Pvar a
      (* OR *)
      | `or_ _, a, Pint (b, _) when Bitvec.(b = zero) -> a
      | `or_ _, Pint (a, _), b when Bitvec.(a = zero) -> b
      | `or_ t, _, Pint (b, _) when Bitvec.(b = ones mod imod t) ->
        Pint (b, t)
      | `or_ t, Pint (a, _), _ when Bitvec.(a = ones mod imod t) ->
        Pint (a, t)
      | `or_ t, Pint (a, _), Pint (b ,_) ->
        Pint (Bitvec.((a lor b) mod imod t), t)
      | `or_ _, Pvar a, Pvar b when Var.(a = b) -> Pvar a
      (* ASR *)
      | `asr_ _, a, Pint (b, _) when Bitvec.(b = zero) -> a
      | `asr_ t, Pint (a, _), Pint (b, _) ->
        Pint (Bitvec.((a asr b) mod imod t), t)
      (* LSL *)
      | `lsl_ _, a, Pint (b, _) when Bitvec.(b = zero) -> a
      | `lsl_ t, Pint (a, _), Pint (b, _) ->
        Pint (Bitvec.((a lsl b) mod imod t), t)
      (* LSR *)
      | `lsr_ _, a, Pint (b, _) when Bitvec.(b = zero) -> a
      | `lsr_ t, Pint (a, _), Pint (b, _) ->
        Pint (Bitvec.((a lsr b) mod imod t), t)
      (* ROL *)
      | `rol _, a, Pint (b, _) when Bitvec.(b = zero) -> a
      | `rol t, Pint (a, _), Pint (b, _) ->
        let sz = Type.sizeof_imm t in
        let m = Bitvec.modulus sz in
        let sh = Bitvec.(((int sz mod m) - b) mod m) in
        let lsh = Bitvec.((a lsl b) mod m) in
        let rsh = Bitvec.((a lsr sh) mod m) in
        Pint (Bitvec.((lsh lor rsh) mod m), t)
      (* ROR *)
      | `ror _, a, Pint (b, _) when Bitvec.(b = zero) -> a
      | `ror t, Pint (a, _), Pint (b, _) ->
        let sz = Type.sizeof_imm t in
        let m = Bitvec.modulus sz in
        let sh = Bitvec.(((int sz mod m) - b) mod m) in
        let lsh = Bitvec.((a lsl sh) mod m) in
        let rsh = Bitvec.((a lsr b) mod m) in
        Pint (Bitvec.((lsh lor rsh) mod m), t)
      (* XOR *)
      | `xor t, Pvar a, Pvar b when Var.(a = b) ->
        Pint (Bitvec.zero, t)
      | `xor _, a, Pint (b, _) when Bitvec.(b = zero) -> a
      | `xor _, Pint (a, _), b when Bitvec.(a = zero) -> b
      | `xor t, Pint (a, _), Pint (b, _) ->
        Pint (Bitvec.((a lxor b) mod imod t), t)
      (* EQ *)
      | `eq #Type.imm, Pint (a, _), Pint (b, _) ->
        Pflag Bitvec.(a = b)
      | `eq #Type.imm, Pvar a, Pvar b when Var.(a = b) ->
        Pflag true
      | `eq `f32, Psingle a, Psingle b ->
        Pflag Float32.(a = b)
      | `eq `f64, Pdouble a, Pdouble b ->
        Pflag Float.(a = b)
      (* GE *)
      | `ge #Type.imm, Pint (a, _), Pint (b, _) ->
        Pflag Bitvec.(a >= b)
      | `ge #Type.imm, Pvar a, Pvar b when Var.(a = b) ->
        Pflag true
      | `ge `f32, Psingle a, Psingle b ->
        Pflag Float32.(a >= b)
      | `ge `f64, Pdouble a, Pdouble b ->
        Pflag Float.(a >= b)
      (* GT *)
      | `gt #Type.imm, Pint (a, _), Pint (b, _) ->
        Pflag Bitvec.(a > b)
      | `gt #Type.imm, Pvar a, Pvar b when Var.(a = b) ->
        Pflag false
      | `gt `f32, Psingle a, Psingle b ->
        Pflag Float32.(a > b)
      | `gt `f64, Pdouble a, Pdouble b ->
        Pflag Float.(a > b)
      (* LE *)
      | `le #Type.imm, Pint (a, _), Pint (b, _) ->
        Pflag Bitvec.(a <= b)
      | `le #Type.imm, Pvar a, Pvar b when Var.(a = b) ->
        Pflag true
      | `le `f32, Psingle a, Psingle b ->
        Pflag Float32.(a <= b)
      | `le `f64, Pdouble a, Pdouble b ->
        Pflag Float.(a <= b)
      (* LT *)
      | `lt #Type.imm, Pint (a, _), Pint (b, _) ->
        Pflag Bitvec.(a < b)
      | `lt #Type.imm, Pvar a, Pvar b when Var.(a = b) ->
        Pflag false
      | `lt `f32, Psingle a, Psingle b ->
        Pflag Float32.(a < b)
      | `lt `f64, Pdouble a, Pdouble b ->
        Pflag Float.(a < b)
      (* NE *)
      | `ne #Type.imm, Pint (a, _), Pint (b, _) ->
        Pflag Bitvec.(a <> b)
      | `ne #Type.imm, Pvar a, Pvar b when Var.(a = b) ->
        Pflag false
      | `ne `f32, Psingle a, Psingle b ->
        Pflag Float32.(a <> b)
      | `ne `f64, Pdouble a, Pdouble b ->
        Pflag Float.(a <> b)
      (* O (ordered) *)
      | `o `f32, Psingle a, Psingle b ->
        Pflag (Float32.is_ordered a b)
      | `o `f64, Pdouble a, Pdouble b ->
        Pflag (Util.float_ordered a b)
      (* SGE *)
      | `sge t, Pint (a, _), Pint (b, _) ->
        Pflag (Util.signed_compare a b @@ imod t >= 0)
      | `sge _, Pvar a, Pvar b when Var.(a = b) ->
        Pflag true
      (* SGT *)
      | `sgt t, Pint (a, _), Pint (b, _) ->
        Pflag (Util.signed_compare a b @@ imod t > 0)
      | `sgt _, Pvar a, Pvar b when Var.(a = b) ->
        Pflag false
      (* SLE *)
      | `sle t, Pint (a, _), Pint (b, _) ->
        Pflag (Util.signed_compare a b @@ imod t <= 0)
      | `sle _, Pvar a, Pvar b when Var.(a = b) ->
        Pflag true
      (* SLT *)
      | `slt t, Pint (a, _), Pint (b, _) ->
        Pflag (Util.signed_compare a b @@ imod t < 0)
      | `slt _, Pvar a, Pvar b when Var.(a = b) ->
        Pflag false
      (* UO (unordered) *)
      | `uo `f32, Psingle a, Psingle b ->
        Pflag (Float32.is_unordered a b)
      | `uo `f64, Pdouble a, Pdouble b ->
        Pflag (Util.float_unordered a b)
      | _, a, b -> Pbinop (l, o, a, b)
    end
  | Pcall (l, t, f, args, vargs) ->
    let args = List.map args ~f:pure in
    let vargs = List.map vargs ~f:pure in
    Pcall (l, t, eval_global f ~env, args, vargs)
  | Pdouble _ | Pflag _ | Pint _ | Psingle _ | Psym _ -> e
  | Pload (l, t, a) -> Pload (l, t, pure a)
  | Psel (l, t, c, y, n) ->
    begin match pure c with
      | Pflag f -> pure @@ if f then y else n
      | c ->  Psel (l, t, c, pure y, pure n)
    end
  | Punop (l, o, a) ->
    begin match o, pure a with
      (* NEG *)
      | `neg #Type.imm, Punop (_, `neg #Type.imm, a) -> a
      | `neg (#Type.imm as t), Pint (a, _) ->
        Pint (Bitvec.((neg a) mod imod t), t)
      | `neg `f32, Psingle a ->
        Psingle (Float32.neg a)
      | `neg `f64, Pdouble a ->
        Pdouble (Float.neg a)
      (* CLZ *)
      | `clz t, Pint (a, _) when Bitvec.(a <> zero) ->
        Pint (Util.clz a @@ Type.sizeof_imm t, t)
      (* CTZ *)
      | `ctz t, Pint (a, _) when Bitvec.(a <> zero) ->
        Pint (Util.ctz a @@ Type.sizeof_imm t, t)
      (* NOT *)
      | `not_ _, Punop (_, `not_ _, a) -> a
      | `not_ t, Pint (a, _) ->
        Pint (Bitvec.((lnot a) mod imod t), t)
      (* POPCNT *)
      | `popcnt t, Pint (a, _) ->
        Pint (Util.popcnt a @@ Type.sizeof_imm t, t)
      (* FEXT *)
      | `fext `f32, (Psingle _ as a) -> a
      | `fext `f64, Psingle a ->
        Pdouble (Float32.to_float a)
      | `fext `f64, (Pdouble _ as a) -> a
      (* FIBITS *)
      | `fibits `f32, Pint (a, _) ->
        Psingle (Float32.of_bits @@ Bitvec.to_int32 a)
      | `fibits `f64, Pint (a, _) ->
        Pdouble (Util.float_of_bits @@ Bitvec.to_int64 a)
      (* FLAG *)
      | `flag t, Pflag f ->
        Pint (Bitvec.bool f, t)
      (* FTOSI *)
      | `ftosi (`f32, `i8), Psingle a ->
        Pint (Util.int8 @@ Float32.to_int8 a, `i8)
      | `ftosi (`f32, `i16), Psingle a ->
        Pint (Util.int16 @@ Float32.to_int16 a, `i16)
      | `ftosi (`f32, `i32), Psingle a ->
        Pint (Util.int32 @@ Float32.to_int32 a, `i32)
      | `ftosi (`f32, `i64), Psingle a ->
        Pint (Util.int64 @@ Float32.to_int64 a, `i64)
      | `ftosi (`f64, `i8), Pdouble a ->
        Pint (Util.int8 @@ Util.float_to_int8 a, `i8)
      | `ftosi (`f64, `i16), Pdouble a ->
        Pint (Util.int16 @@ Util.float_to_int16 a, `i16)
      | `ftosi (`f64, `i32), Pdouble a ->
        Pint (Util.int32 @@ Util.float_to_int32 a, `i32)
      | `ftosi (`f64, `i64), Pdouble a ->
        Pint (Util.int64 @@ Util.float_to_int64 a, `i64)
      (* FTOUI *)
      | `ftoui (`f32, `i8), Psingle a ->
        Pint (Util.int8 @@ Float32.to_uint8 a, `i8)
      | `ftoui (`f32, `i16), Psingle a ->
        Pint (Util.int16 @@ Float32.to_uint16 a, `i16)
      | `ftoui (`f32, `i32), Psingle a ->
        Pint (Util.int32 @@ Float32.to_uint32 a, `i32)
      | `ftoui (`f32, `i64), Psingle a ->
        Pint (Util.int64 @@ Float32.to_uint64 a, `i64)
      | `ftoui (`f64, `i8), Pdouble a ->
        Pint (Util.int8 @@ Util.float_to_uint8 a, `i8)
      | `ftoui (`f64, `i16), Pdouble a ->
        Pint (Util.int16 @@ Util.float_to_uint16 a, `i16)
      | `ftoui (`f64, `i32), Pdouble a ->
        Pint (Util.int32 @@ Util.float_to_uint32 a, `i32)
      | `ftoui (`f64, `i64), Pdouble a ->
        Pint (Util.int64 @@ Util.float_to_uint64 a, `i64)
      (* FTRUNC *)
      | `ftrunc `f32, (Psingle _ as a) -> a
      | `ftrunc `f32, Pdouble a ->
        Psingle (Float32.of_float a)
      (* IFBITS *)
      | `ifbits t, Psingle a ->
        let t = (t :> Type.imm) in
        Pint (Bitvec.(int32 (Float32.bits a) mod imod t), t)
      | `ifbits t, Pdouble a ->
        let t = (t :> Type.imm) in
        Pint (Bitvec.(int64 (Util.float_to_bits a) mod imod t), t)
      (* ITRUNC *)
      | `itrunc t, (Pint (_, i) as a) when Type.equal_imm t i -> a
      | `itrunc t, Pint (a, _) ->
        let hi = Type.sizeof_imm t -  1 in
        Pint (Bitvec.extract ~hi ~lo:0 a, t)
      (* SEXT *)
      | `sext t, (Pint (_, i) as a) when Type.equal_imm t i -> a
      | `sext t, Pint (a, t') ->
        let sz' = Type.sizeof_imm t' in
        let m' = Bitvec.modulus sz' in
        if Bitvec.(msb a mod m') then
          let m = imod t in
          let sh = Bitvec.(int sz' mod m) in
          Pint (Bitvec.(((((ones mod m) lsl sh) mod m) lor a) mod m), t)
        else Pint (a, t)
      (* SITOF *)
      | `sitof (`i8, `f32), Pint (a, _) ->
        Psingle (Float32.of_int8 @@ Bitvec.to_int a)
      | `sitof (`i16, `f32), Pint (a, _) ->
        Psingle (Float32.of_int16 @@ Bitvec.to_int a)
      | `sitof (`i32, `f32), Pint (a, _) ->
        Psingle (Float32.of_int32 @@ Bitvec.to_int32 a)
      | `sitof (`i64, `f32), Pint (a, _) ->
        Psingle (Float32.of_int64 @@ Bitvec.to_int64 a)
      | `sitof (`i8, `f64), Pint (a, _) ->
        Pdouble (Util.float_of_int8 @@ Bitvec.to_int a)
      | `sitof (`i16, `f64), Pint (a, _) ->
        Pdouble (Util.float_of_int16 @@ Bitvec.to_int a)
      | `sitof (`i32, `f64), Pint (a, _) ->
        Pdouble (Util.float_of_int32 @@ Bitvec.to_int32 a)
      | `sitof (`i64, `f64), Pint (a, _) ->
        Pdouble (Util.float_of_int64 @@ Bitvec.to_int64 a)
      (* UITOF *)
      | `uitof (`i8, `f32), Pint (a, _) ->
        Psingle (Float32.of_uint8 @@ Bitvec.to_int a)
      | `uitof (`i16, `f32), Pint (a, _) ->
        Psingle (Float32.of_uint16 @@ Bitvec.to_int a)
      | `uitof (`i32, `f32), Pint (a, _) ->
        Psingle (Float32.of_uint32 @@ Bitvec.to_int32 a)
      | `uitof (`i64, `f32), Pint (a, _) ->
        Psingle (Float32.of_uint64 @@ Bitvec.to_int64 a)
      | `uitof (`i8, `f64), Pint (a, _) ->
        Pdouble (Util.float_of_uint8 @@ Bitvec.to_int a)
      | `uitof (`i16, `f64), Pint (a, _) ->
        Pdouble (Util.float_of_uint16 @@ Bitvec.to_int a)
      | `uitof (`i32, `f64), Pint (a, _) ->
        Pdouble (Util.float_of_uint32 @@ Bitvec.to_int32 a)
      | `uitof (`i64, `f64), Pint (a, _) ->
        Pdouble (Util.float_of_uint64 @@ Bitvec.to_int64 a)
      (* ZEXT *)
      | `zext t, Pint (a, _) ->
        Pint (a, t)
      (* COPY *)
      | `copy _, (Pdouble _ | Pint _ | Psingle _ | Psym _ | Pvar _ as a) -> a
      | _, a -> Punop (l, o, a)
    end
  | Pvar v -> Map.find env v |> Option.value ~default:e

and eval_global ?(env = Var.Map.empty) = function
  | (Gaddr _ | Gsym _) as g -> g
  | Gpure p -> Gpure (eval_pure p ~env)

let eval_local ?(env = Var.Map.empty) (l, args) =
  l, List.map args ~f:(eval_pure ~env)

let eval_dst ?(env = Var.Map.empty) = function
  | Dglobal g -> Dglobal (eval_global ~env g)
  | Dlocal l -> Dlocal (eval_local ~env l)

let eval_table ?(env = Var.Map.empty) tbl =
  List.map tbl ~f:(fun (i, l) -> i, eval_local ~env l)

let find_table tbl i d =
  List.Assoc.find tbl i ~equal:Bitvec.equal |>
  Option.value ~default:d

let eval ?(env = Var.Map.empty) e =
  let pure = eval_pure ~env in
  let local = eval_local ~env in
  let dst = eval_dst ~env in
  match e with
  | Ebr (c, y, n) ->
    begin match pure c with
      | Pflag f -> Ejmp (dst @@ if f then y else n)
      | c -> Ebr (c, dst y, dst n)
    end
  | Ecall (f, args, vargs) ->
    let args = List.map args ~f:pure in
    let vargs = List.map vargs ~f:pure in
    Ecall (eval_global ~env f, args, vargs)
  | Ehlt | Eret None | Evaarg _ | Evastart _ -> e
  | Ejmp d -> Ejmp (dst d)
  | Eret Some r -> Eret (Some (pure r))
  | Eset (x, p) -> Eset (x, pure p)
  | Estore (t, v, a) -> Estore (t, pure v, pure a)
  | Esw (t, i, d, tbl) -> match pure i with
    | Pint (x, _) -> Ejmp (Dlocal (local @@ find_table tbl x d))
    | i -> Esw (t, i, local d, eval_table ~env tbl)
