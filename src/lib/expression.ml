open Core
open Graphlib.Std
open Monads.Std
open Regular.Std
open Virtual

module Bitvec = struct
  include Bitvec
  include Bitvec_binprot
  include Bitvec_order
  include Bitvec_sexp
end

module E = Monad.Result.Error

open E.Let

type pure =
  | Palloc  of Label.t * int
  | Pbinop  of Label.t * Insn.binop * pure * pure
  | Pcall   of Label.t * Type.basic * global * pure list * pure list
  | Pdouble of float
  | Pflag   of bool
  | Pint    of Bitvec.t * Type.imm
  | Pload   of Label.t * Type.basic * pure
  | Psel    of Label.t * Type.basic * pure * pure * pure
  | Psingle of Float32.t
  | Psym    of string * int
  | Punop   of Label.t * Insn.unop * pure
  | Pvar    of Var.t
[@@deriving bin_io, compare, equal, sexp]

and global =
  | Gaddr of Bitvec.t
  | Gpure of pure
  | Gsym  of string
[@@deriving bin_io, compare, equal, sexp]

and local = Label.t * pure list
[@@deriving bin_io, compare, equal, sexp]

and dst =
  | Dglobal of global
  | Dlocal  of local
[@@deriving bin_io, compare, equal, sexp]

type table = (Bitvec.t * local) list
[@@deriving bin_io, compare, equal, sexp]

type t =
  | Ebr      of pure * dst * dst
  | Ecall    of global * pure list * pure list
  | Ehlt
  | Ejmp     of dst
  | Eret     of pure option
  | Eset     of Var.t * pure
  | Estore   of Type.basic * pure * pure
  | Esw      of Type.imm * pure * local * table
  | Evaarg   of Var.t * Type.basic * Var.t
  | Evastart of Var.t
[@@deriving bin_io, compare, equal, sexp]

module Eval = struct
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
        Pflag (Eval.float_ordered a b)
      (* SGE *)
      | `sge t, Pint (a, _), Pint (b, _) ->
        Pflag (Eval.signed_compare a b @@ imod t >= 0)
      | `sge _, Pvar a, Pvar b when Var.(a = b) ->
        Pflag true
      (* SGT *)
      | `sgt t, Pint (a, _), Pint (b, _) ->
        Pflag (Eval.signed_compare a b @@ imod t > 0)
      | `sgt _, Pvar a, Pvar b when Var.(a = b) ->
        Pflag false
      (* SLE *)
      | `sle t, Pint (a, _), Pint (b, _) ->
        Pflag (Eval.signed_compare a b @@ imod t <= 0)
      | `sle _, Pvar a, Pvar b when Var.(a = b) ->
        Pflag true
      (* SLT *)
      | `slt t, Pint (a, _), Pint (b, _) ->
        Pflag (Eval.signed_compare a b @@ imod t < 0)
      | `slt _, Pvar a, Pvar b when Var.(a = b) ->
        Pflag false
      (* UO (unordered) *)
      | `uo `f32, Psingle a, Psingle b ->
        Pflag (Float32.is_unordered a b)
      | `uo `f64, Pdouble a, Pdouble b ->
        Pflag (Eval.float_unordered a b)
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
        Pint (Eval.clz a @@ Type.sizeof_imm t, t)
      (* CTZ *)
      | `ctz t, Pint (a, _) when Bitvec.(a <> zero) ->
        Pint (Eval.ctz a @@ Type.sizeof_imm t, t)
      (* NOT *)
      | `not_ _, Punop (_, `not_ _, a) -> a
      | `not_ t, Pint (a, _) ->
        Pint (Bitvec.((lnot a) mod imod t), t)
      (* POPCNT *)
      | `popcnt t, Pint (a, _) ->
        Pint (Eval.popcnt a @@ Type.sizeof_imm t, t)
      (* FEXT *)
      | `fext `f32, (Psingle _ as a) -> a
      | `fext `f64, Psingle a ->
        Pdouble (Float32.to_float a)
      | `fext `f64, (Pdouble _ as a) -> a
      (* FIBITS *)
      | `fibits `f32, Pint (a, _) ->
        Psingle (Float32.of_bits @@ Bitvec.to_int32 a)
      | `fibits `f64, Pint (a, _) ->
        Pdouble (Eval.float_of_bits @@ Bitvec.to_int64 a)
      (* FLAG *)
      | `flag t, Pflag f ->
        Pint (Bitvec.bool f, t)
      (* FTOSI *)
      | `ftosi (`f32, `i8), Psingle a ->
        Pint (Eval.int8 @@ Float32.to_int8 a, `i8)
      | `ftosi (`f32, `i16), Psingle a ->
        Pint (Eval.int16 @@ Float32.to_int16 a, `i16)
      | `ftosi (`f32, `i32), Psingle a ->
        Pint (Eval.int32 @@ Float32.to_int32 a, `i32)
      | `ftosi (`f32, `i64), Psingle a ->
        Pint (Eval.int64 @@ Float32.to_int64 a, `i64)
      | `ftosi (`f64, `i8), Pdouble a ->
        Pint (Eval.int8 @@ Eval.float_to_int8 a, `i8)
      | `ftosi (`f64, `i16), Pdouble a ->
        Pint (Eval.int16 @@ Eval.float_to_int16 a, `i16)
      | `ftosi (`f64, `i32), Pdouble a ->
        Pint (Eval.int32 @@ Eval.float_to_int32 a, `i32)
      | `ftosi (`f64, `i64), Pdouble a ->
        Pint (Eval.int64 @@ Eval.float_to_int64 a, `i64)
      (* FTOUI *)
      | `ftoui (`f32, `i8), Psingle a ->
        Pint (Eval.int8 @@ Float32.to_uint8 a, `i8)
      | `ftoui (`f32, `i16), Psingle a ->
        Pint (Eval.int16 @@ Float32.to_uint16 a, `i16)
      | `ftoui (`f32, `i32), Psingle a ->
        Pint (Eval.int32 @@ Float32.to_uint32 a, `i32)
      | `ftoui (`f32, `i64), Psingle a ->
        Pint (Eval.int64 @@ Float32.to_uint64 a, `i64)
      | `ftoui (`f64, `i8), Pdouble a ->
        Pint (Eval.int8 @@ Eval.float_to_uint8 a, `i8)
      | `ftoui (`f64, `i16), Pdouble a ->
        Pint (Eval.int16 @@ Eval.float_to_uint16 a, `i16)
      | `ftoui (`f64, `i32), Pdouble a ->
        Pint (Eval.int32 @@ Eval.float_to_uint32 a, `i32)
      | `ftoui (`f64, `i64), Pdouble a ->
        Pint (Eval.int64 @@ Eval.float_to_uint64 a, `i64)
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
        Pint (Bitvec.(int64 (Eval.float_to_bits a) mod imod t), t)
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
        Pdouble (Eval.float_of_int8 @@ Bitvec.to_int a)
      | `sitof (`i16, `f64), Pint (a, _) ->
        Pdouble (Eval.float_of_int16 @@ Bitvec.to_int a)
      | `sitof (`i32, `f64), Pint (a, _) ->
        Pdouble (Eval.float_of_int32 @@ Bitvec.to_int32 a)
      | `sitof (`i64, `f64), Pint (a, _) ->
        Pdouble (Eval.float_of_int64 @@ Bitvec.to_int64 a)
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
        Pdouble (Eval.float_of_uint8 @@ Bitvec.to_int a)
      | `uitof (`i16, `f64), Pint (a, _) ->
        Pdouble (Eval.float_of_uint16 @@ Bitvec.to_int a)
      | `uitof (`i32, `f64), Pint (a, _) ->
        Pdouble (Eval.float_of_uint32 @@ Bitvec.to_int32 a)
      | `uitof (`i64, `f64), Pint (a, _) ->
        Pdouble (Eval.float_of_uint64 @@ Bitvec.to_int64 a)
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

module Deps = Graphlib.Make(Label)(Var)

type ctx = {
  func         : string;
  insns        : (insn * blk) Label.Map.t;
  blks         : blk Label.Map.t;
  cfg          : Cfg.t;
  pure         : pure Var.Table.t;
  exp          : t Label.Table.t;
  filled       : Var.Hash_set.t;
  mutable deps : Deps.t;
}

let map_of_insns fn =
  let init = Label.Map.empty in
  Func.blks fn |> E.Seq.fold ~init ~f:(fun init blk ->
      Blk.insns blk |> E.Seq.fold ~init ~f:(fun m i ->
          let key = Insn.label i in
          match Map.add m ~key ~data:(i, blk) with
          | `Ok m -> Ok m
          | `Duplicate ->
            E.failf "Duplicate label for instruction %a in block %a"
              Label.pp key Label.pp (Blk.label blk) ()))

let init fn =
  let+ insns = map_of_insns fn in
  let blks = Func.map_of_blks fn in
  let cfg = Cfg.create fn in
  let pure = Var.Table.create () in
  let exp = Label.Table.create () in
  let filled = Var.Hash_set.create () in
  let func = Func.name fn in
  {func; insns; blks; cfg; pure; exp; filled; deps = Deps.empty}

let func ctx = ctx.func

type resolved = [
  | `blk  of blk
  | `insn of insn * blk
]

let resolve ctx l = match Map.find ctx.blks l with
  | Some b -> Some (`blk b)
  | None -> match Map.find ctx.insns l with
    | Some x -> Some (`insn x)
    | None -> None

let dependents ctx src =
  Deps.Node.succs src ctx.deps |>
  Seq.filter_map ~f:(fun dst ->
      Deps.Node.edge src dst ctx.deps |>
      Option.map ~f:(fun e -> dst, Deps.Edge.label e))

let dependencies ctx dst =
  Deps.Node.preds dst ctx.deps |>
  Seq.filter_map ~f:(fun src ->
      Deps.Node.edge src dst ctx.deps |>
      Option.map ~f:(fun e -> src, Deps.Edge.label e))

let pp_deps ppf ctx =
  Graphlib.Dot.pp_graph
    ~string_of_node:Label.to_string
    ~node_label:Label.to_string
    ~edge_label:(fun e -> Var.to_string @@ Deps.Edge.label e)
    ~nodes_of_edge:(fun e -> Deps.Edge.(src e, dst e))
    ~nodes:(Deps.nodes ctx.deps)
    ~edges:(Deps.edges ctx.deps)
    ppf

let rec free_vars_of_pure = function
  | Palloc _ | Pdouble _ | Pflag _ | Pint _ | Psingle _ | Psym _ ->
    Var.Set.empty
  | Pbinop (_, _, a, b) ->
    Set.union (free_vars_of_pure a) (free_vars_of_pure b)
  | Pcall (_, _, f, args, vargs) ->
    let args = List.map args ~f:free_vars_of_pure in
    let vargs = List.map vargs ~f:free_vars_of_pure in
    Var.Set.union_list (free_vars_of_global f :: (args @ vargs))
  | Pload (_, _, a) | Punop (_, _, a) -> free_vars_of_pure a
  | Psel (_, _, c, t, f) ->
    Var.Set.union_list [
      free_vars_of_pure c;
      free_vars_of_pure t;
      free_vars_of_pure f;
    ]
  | Pvar v -> Var.Set.singleton v

and free_vars_of_global = function
  | Gaddr _ | Gsym _ -> Var.Set.empty
  | Gpure p -> free_vars_of_pure p

let free_vars_of_local (_, args) =
  List.map args ~f:free_vars_of_pure |> Var.Set.union_list

let free_vars_of_dst = function
  | Dglobal g -> free_vars_of_global g
  | Dlocal l -> free_vars_of_local l

let free_vars_of_table tbl =
  List.map tbl ~f:(fun (_, l) -> free_vars_of_local l) |>
  Var.Set.union_list

let free_vars = function
  | Ebr (c, t, f) ->
    Var.Set.union_list [
      free_vars_of_pure c;
      free_vars_of_dst t;
      free_vars_of_dst f;
    ]
  | Ecall (f, args, vargs) ->
    let args = List.map args ~f:free_vars_of_pure in
    let vargs = List.map vargs ~f:free_vars_of_pure in
    Var.Set.union_list (free_vars_of_global f :: (args @ vargs))
  | Ehlt | Eret None -> Var.Set.empty
  | Ejmp d -> free_vars_of_dst d
  | Eret (Some p) | Eset (_, p) -> free_vars_of_pure p
  | Estore (_, v, a) ->
    Set.union (free_vars_of_pure v) (free_vars_of_pure a)
  | Esw (_, i, d, tbl) ->
    Var.Set.union_list [
      free_vars_of_pure i;
      free_vars_of_local d;
      free_vars_of_table tbl;
    ]
  | Evaarg (_, _, v) | Evastart v ->
    Var.Set.singleton v

let rec labels_of_pure = function
  | Palloc (l, _) -> Label.Set.singleton l
  | Pbinop (l, _, a, b) ->
    let a = labels_of_pure a in
    let b = labels_of_pure b in
    Set.(add (union a b) l)
  | Pcall (l, _, f, args, vargs) ->
    let f = labels_of_global f in
    let args = List.map args ~f:labels_of_pure in
    let vargs = List.map vargs ~f:labels_of_pure in
    Label.Set.(add (union_list (f :: (args @ vargs))) l)
  | Pdouble _ | Pflag _ | Pint _ | Psingle _ | Psym _ | Pvar _ ->
    Label.Set.empty
  | Pload (l, _, a) -> Set.(add (labels_of_pure a) l)
  | Psel (l, _, c, t, f) ->
    let c = labels_of_pure c in
    let t = labels_of_pure t in
    let f = labels_of_pure f in
    Label.Set.(add (union_list [c; t; f]) l)
  | Punop (l, _, a) -> Set.(add (labels_of_pure a) l)

and labels_of_global = function
  | Gaddr _ | Gsym _ -> Label.Set.empty
  | Gpure p -> labels_of_pure p

let labels_of_local (_, args) =
  List.map args ~f:labels_of_pure |>
  Label.Set.union_list

let labels_of_dst = function
  | Dglobal g -> labels_of_global g
  | Dlocal l -> labels_of_local l

let labels_of_table tbl =
  List.map tbl ~f:(fun (_, l) -> labels_of_local l) |>
  Label.Set.union_list

let labels = function
  | Ebr (c, t, f) ->
    Label.Set.union_list [
      labels_of_pure c;
      labels_of_dst t;
      labels_of_dst f;
    ]
  | Ecall (f, args, vargs) ->
    let f = labels_of_global f in
    let args = List.map args ~f:labels_of_pure in
    let vargs = List.map vargs ~f:labels_of_pure in
    Label.Set.union_list (f :: (args @ vargs))
  | Ehlt | Eret None | Evaarg _ | Evastart _ -> Label.Set.empty
  | Ejmp d -> labels_of_dst d
  | Eret (Some p) | Eset (_, p) -> labels_of_pure p
  | Estore (_, v, a) ->
    Set.union (labels_of_pure v) (labels_of_pure a)
  | Esw (_, i, d, tbl) ->
    Label.Set.union_list [
      labels_of_pure i;
      labels_of_local d;
      labels_of_table tbl;
    ]

exception Occurs_failed of Var.t * Label.t option

(* Keep track of the set of variables we're substituting. If
   we find a cycle in the dependency chain then the function
   is probably not in SSA form. *)
let rec subst_pure ?(vs = Var.Set.empty) ctx e =
  let go = subst_pure ctx ~vs in
  match e with
  | Palloc _ as a -> a
  | Pbinop (l, o, x, y) ->
    Pbinop (l, o, go x, go y)
  | Pcall (l, t, f, args, vargs) ->
    let args = List.map args ~f:go in
    let vargs = List.map vargs ~f:go in
    Pcall (l, t, subst_global ctx f ~vs, args, vargs)
  | Pdouble _ | Pflag _ | Pint _ | Psingle _ | Psym _ -> e
  | Pload (l, t, a) -> Pload (l, t, go a)
  | Psel (l, t, c, y, n) -> Psel (l, t, go c, go y, go n)
  | Punop (l, o, x) -> Punop (l, o, go x)
  | Pvar x when Set.mem vs x -> raise @@ Occurs_failed (x, None)
  | Pvar x as default ->
    Hashtbl.find ctx.pure x |>
    Option.value_map ~default ~f:(continue x vs ctx)

(* Make the full substitution on subterms and cache the results. *)
and continue x vs ctx = function
  | (Palloc _ | Pdouble _ | Pflag _ | Pint _ | Psingle _ | Psym _) as e -> e
  | e when Hash_set.mem ctx.filled x -> e
  | e ->
    let e = subst_pure ctx e ~vs:(Set.add vs x) in
    Hashtbl.set ctx.pure ~key:x ~data:e;
    Hash_set.add ctx.filled x;
    e

and subst_global ?(vs = Var.Set.empty) ctx = function
  | (Gaddr _ | Gsym _) as g -> g
  | Gpure p -> Gpure (subst_pure ctx p ~vs)

let subst_local ctx (l, args) = l, List.map args ~f:(subst_pure ctx)

let subst_dst ctx = function
  | Dglobal g -> Dglobal (subst_global ctx g)
  | Dlocal l -> Dlocal (subst_local ctx l)

let rec pp_args args =
  let pp_sep ppf () = Format.fprintf ppf ", " in
  (Format.pp_print_list ~pp_sep pp_pure) args

and pp_pure ppf = function
  | Palloc (l, n) ->
    Format.fprintf ppf "alloc%a(%d)" Label.pp l n
  | Pbinop (l, o, x, y) ->
    Format.fprintf ppf "%a%a(%a, %a)"
      Insn.pp_binop o Label.pp l pp_pure x pp_pure y
  | Pcall (l, _t, f, [], []) ->
    Format.fprintf ppf "%a%a()" pp_global f Label.pp l
  | Pcall (l, _t, f, args, []) ->
    Format.fprintf ppf "%a%a(%a)"
      pp_global f Label.pp l pp_args args
  | Pcall (l, _t, f, [], vargs) ->
    Format.fprintf ppf "%a%a(..., %a)"
      pp_global f Label.pp l pp_args vargs
  | Pcall (l, _t, f, args, vargs) ->
    Format.fprintf ppf "%a%a(%a, ..., %a)"
      pp_global f Label.pp l pp_args args pp_args vargs
  | Pdouble d ->
    Format.fprintf ppf "%a_d" Float.pp d
  | Pflag f ->
    Format.fprintf ppf "%a" Bool.pp f
  | Pint (i, t) ->
    Format.fprintf ppf "%a_%a" Bitvec.pp i Type.pp_imm t
  | Pload (l, t, a) ->
    Format.fprintf ppf "ld.%a%a(%a)"
      Type.pp_basic t Label.pp l pp_pure a
  | Psel (l, t, c, y, n) ->
    Format.fprintf ppf "sel.%a%a(%a, %a, %a)"
      Type.pp_basic t Label.pp l pp_pure c pp_pure y pp_pure n
  | Psingle s ->
    Format.fprintf ppf "%s_s" @@ Float32.to_string s
  | Psym (s, o) ->
    if o = 0 then Format.fprintf ppf "$%s" s
    else if o < 0 then Format.fprintf ppf "$%s-%d" s (lnot o + 1) 
    else Format.fprintf ppf "$%s+%d" s o
  | Punop (l, o, x) ->
    Format.fprintf ppf "%a%a(%a)"
      Insn.pp_unop o Label.pp l pp_pure x
  | Pvar v ->
    Format.fprintf ppf "%a" Var.pp v

and pp_global ppf = function
  | Gaddr a ->
    Format.fprintf ppf "%a" Bitvec.pp a
  | Gpure p ->
    Format.fprintf ppf "%a" pp_pure p
  | Gsym s ->
    Format.fprintf ppf "$%s" s

let pp_local ppf = function
  | l, [] ->
    Format.fprintf ppf "%a" Label.pp l
  | l, args ->
    Format.fprintf ppf "%a(%a)" Label.pp l pp_args args

let pp_dst ppf = function
  | Dglobal g ->
    Format.fprintf ppf "%a" pp_global g
  | Dlocal l ->
    Format.fprintf ppf "%a" pp_local l

let subst_table m = List.map ~f:(fun (i, l) -> i, subst_local m l)

let pp_table tbl =
  let pp_sep ppf () = Format.fprintf ppf "," in
  let pp ppf (v, l) = Format.fprintf ppf "%a:%a" Bitvec.pp v pp_local l in
  (Format.pp_print_list ~pp_sep pp) tbl

let subst ctx e =
  let pure = subst_pure ctx in
  let dst = subst_dst ctx in
  match e with
  | Ebr (c, y, n) -> Ebr (pure c, dst y, dst n)
  | Ecall (f, args, vargs) ->
    let args = List.map args ~f:pure in
    let vargs = List.map vargs ~f:pure in
    Ecall (subst_global ctx f, args, vargs)
  | Ejmp d -> Ejmp (subst_dst ctx d)
  | Eret None as r -> r
  | Eret (Some p) -> Eret (Some (subst_pure ctx p))
  | Eset (x, y) -> Eset (x, subst_pure ctx y ~vs:(Var.Set.singleton x))
  | Estore (t, v, a) -> Estore (t, pure v, pure a)
  | Esw (t, v, d, tbl) ->
    Esw (t, pure v, subst_local ctx d, subst_table ctx tbl)
  | (Ehlt | Evaarg _ | Evastart _) as e -> e

let pp ppf = function
  | Ebr (c, t, f) ->
    Format.fprintf ppf "br(%a, %a, %a)"
      pp_pure c pp_dst t pp_dst f
  | Ecall (f, [], []) ->
    Format.fprintf ppf "%a()" pp_global f
  | Ecall (f, args, []) ->
    Format.fprintf ppf "%a(%a)" pp_global f pp_args args
  | Ecall (f, [], vargs) ->
    Format.fprintf ppf "%a(..., %a)" pp_global f pp_args vargs
  | Ecall (f, args, vargs) ->
    Format.fprintf ppf "%a(%a, ..., %a)"
      pp_global f pp_args args pp_args vargs
  | Ehlt ->
    Format.fprintf ppf "hlt"
  | Ejmp d ->
    Format.fprintf ppf "jmp(%a)" pp_dst d
  | Eret (Some x) ->
    Format.fprintf ppf "ret(%a)" pp_pure x
  | Eret None ->
    Format.fprintf ppf "ret"
  | Eset (x, y) ->
    Format.fprintf ppf "%a = %a" Var.pp x pp_pure y
  | Estore (t, v, a) ->
    Format.fprintf ppf "st%a(%a, %a)"
      Type.pp_basic t pp_pure v pp_pure a
  | Esw (t, v, d, tbl) ->
    Format.fprintf ppf "sw.%a(%a, %a, [%a])"
      Type.pp_imm t pp_pure v pp_local d pp_table tbl
  | Evaarg (x, t, y) ->
    Format.fprintf ppf "%a = vaarg.%a(%a)"
      Var.pp x Type.pp_basic t Var.pp y
  | Evastart x ->
    Format.fprintf ppf "vastart(%a)" Var.pp x

module Builder : sig
  val of_ctrl : ctx -> blk -> t
  val of_insn : ctx -> insn -> blk -> t
end = struct
  (* The worklist keeps track of the dependencies that the
     algorithm should attempt to resolve. It also helps us
     construct the dependency graph on the fly. *)
  module Worklist : sig
    type t 

    val empty : t
    val is_empty : t -> bool
    val remove : t -> Var.t -> t
    val mem : t -> Var.t -> bool
    val singleton : Var.t -> Label.t -> t
    val add : t -> Var.t -> Label.t -> t
    val graph : t -> Label.t -> Var.t -> Deps.t -> Deps.t
  end = struct
    type t = Label.Set.t Var.Map.t

    let empty = Var.Map.empty
    let is_empty = Map.is_empty
    let remove = Map.remove
    let mem = Map.mem

    let singleton x l =
      Var.Map.singleton x @@ Label.Set.singleton l

    let add w x l = Map.update w x ~f:(function
        | None -> Label.Set.singleton l
        | Some s -> Set.add s l)

    let graph w src x g =
      Map.find w x |> Option.value_map ~default:g ~f:(fun s ->
          Set.fold s ~init:g ~f:(fun g dst ->
              let e = Deps.Edge.create src dst x in
              Deps.Edge.insert e g))
  end

  let operand (o : operand) w l = match o with
    | `int (i, t) -> Pint (i, t), w
    | `float f    -> Psingle f, w
    | `double d   -> Pdouble d, w
    | `sym (s, o) -> Psym (s, o), w
    | `var v      -> Pvar v, Worklist.add w v l

  let operands os w l =
    List.fold_right os ~init:([], w) ~f:(fun o (os, w) ->
        let o, w = operand o w l in
        o :: os, w)

  let global (g : Virtual.global) w l = match g with
    | `addr a -> Gaddr a, w
    | `sym s  -> Gsym s, w
    | `var v  -> Gpure (Pvar v), Worklist.add w v l

  let local (loc : Virtual.local) w l = match loc with
    | `label (lbl, args) ->
      let args, w = operands args w l in
      (lbl, args), w

  let dst (d : Virtual.dst) w l = match d with
    | #Virtual.global as g ->
      let g, w = global g w l in
      Dglobal g, w
    | #Virtual.local as loc ->
      let loc, w = local loc w l in
      Dlocal loc, w

  let table tbl w l =
    let tbl, w =
      Ctrl.Table.enum tbl |>
      Seq.fold ~init:([], w) ~f:(fun (tbl, w) (i, loc) ->
          let loc, w = local loc w l in
          (i, loc) :: tbl, w) in
    List.rev tbl, w

  let update ctx l ((w, xs) as acc) x f =
    (* Fail if we've already seen this variable. *)
    if Set.mem xs x then
      raise @@ Occurs_failed (x, Some l);
    if Worklist.mem w x then
      let w' = ref @@ Worklist.remove w x in
      (* Assume that the current bound expression is the same. *)
      if not @@ Hashtbl.mem ctx.pure x then begin
        let w, p = f !w' in
        (* Fail early if we re-introduce the same variable. *)
        if Worklist.mem w x then
          raise @@ Occurs_failed (x, Some l);
        Hashtbl.set ctx.pure ~key:x ~data:p;
        w' := w;
      end;
      ctx.deps <- Worklist.graph w l x ctx.deps;
      !w', Set.add xs x
    else acc

  (* Accumulate the results of an instruction. *)
  let accum ctx acc i =
    let l = Insn.label i in
    let go = update ctx l acc in
    match Insn.op i with
    | `bop (x, o, a, b) -> go x @@ fun w ->
      let a, w = operand a w l in
      let b, w = operand b w l in
      w, Pbinop (l, o, a, b)
    | `uop (x, o, a) -> go x @@ fun w ->
      let a, w = operand a w l in
      w, Punop (l, o, a)
    | `sel (x, t, c, y, n) -> go x @@ fun w ->
      let c, w = Pvar c, Worklist.add w c l in
      let y, w = operand y w l in
      let n, w = operand n w l in
      w, Psel (l, t, c, y, n)
    | `call (Some (x, t), f, args, vargs) -> go x @@ fun w ->
      let f, w = global f w l in
      let args, w = operands args w l in
      let vargs, w = operands vargs w l in
      w, Pcall (l, t, f, args, vargs)
    | `alloc (x, n) -> go x @@ fun w -> w, Palloc (l, n)
    | `load (x, t, a) -> go x @@ fun w ->
      let a, w = operand a w l in
      w, Pload (l, t, a)
    | _ -> acc

  (* Kill the variables that appear in the arguments of the block.
     This is the point where we can no longer represent their data
     dependencies as a DAG. *)
  let killed blk w =
    Blk.args blk |> Seq.map ~f:fst |>
    Seq.fold ~init:w ~f:Worklist.remove

  let different_insn l i = Label.(l <> Insn.label i)

  let subseq blk l ss =
    if Label.(l <> Blk.label blk) then
      Seq.drop_while_option ss ~f:(different_insn l) |>
      Option.value_map ~default:Seq.empty ~f:snd
    else ss

  let insns ctx blk l w xs =
    let w, xs =
      Blk.insns blk ~rev:true |> subseq blk l |>
      Seq.fold ~init:(w, xs) ~f:(accum ctx) in
    killed blk w, xs

  (* Next blocks to visit. *)
  let nexts ctx blk bs =
    Cfg.Node.preds (Blk.label blk) ctx.cfg |>
    Seq.filter_map ~f:(fun l ->
        if Label.is_pseudo l || Set.mem bs l
        then None else Map.find ctx.blks l)

  let initq blk l w =
    blk, l, w, Label.Set.empty, Var.Set.empty

  (* Traverse the data dependencies. *)
  let traverse ctx blk l w =
    if not @@ Worklist.is_empty w then
      let q = Stack.singleton @@ initq blk l w in
      while not @@ Stack.is_empty q do
        let blk, l, w, bs, xs = Stack.pop_exn q in
        let w, xs = insns ctx blk l w xs in
        if not @@ Worklist.is_empty w then
          let bs = Set.add bs @@ Blk.label blk in
          nexts ctx blk bs |> Seq.iter ~f:(fun blk ->
              Stack.push q (blk, Blk.label blk, w, bs, xs))
      done

  let run ctx blk l f =
    let w, e = f () in
    traverse ctx blk l w;
    let e = subst ctx e in
    Hashtbl.set ctx.exp ~key:l ~data:e;
    e

  let of_ctrl ctx blk =
    let l = Blk.label blk in
    let go = run ctx blk l in
    match Blk.ctrl blk with
    | `hlt -> Ehlt
    | `jmp d -> go @@ fun () ->
      let d, w = dst d Worklist.empty l in
      w, Ejmp d
    | `br (c, y, n) -> go @@ fun () ->
      let c, w = Pvar c, Worklist.singleton c l in
      let y, w = dst y w l in
      let n, w = dst n w l in
      w, Ebr (c, y, n)
    | `ret None -> Eret None
    | `ret (Some x) -> go @@ fun () ->
      let x, w = operand x Worklist.empty l in
      w, Eret (Some x)
    | `sw (t, v, d, tbl) -> go @@ fun () ->
      let v, w = Pvar v, Worklist.singleton v l in
      let d, w = local d w l in
      let tbl, w = table tbl w l in
      w, Esw (t, v, d, tbl)

  let of_insn ctx i blk =
    let l = Insn.label i in
    let go = run ctx blk l in
    match Insn.op i with
    | `bop (x, o, a, b) -> go @@ fun () ->
      let a, w = operand a Worklist.empty l in
      let b, w = operand b w l in
      w, Eset (x, Pbinop (l, o, a, b))
    | `uop (x, o, a) -> go @@ fun () ->
      let a, w = operand a Worklist.empty l in
      w, Eset (x, Punop (l, o, a))
    | `sel (x, t, c, y, n) -> go @@ fun () ->
      let y, w = operand y (Worklist.singleton c l) l in
      let n, w = operand n w l in
      w, Eset (x, Psel (l, t, Pvar c, y, n))
    | `call (Some (x, t), f, args, vargs) -> go @@ fun () ->
      let f, w = global f Worklist.empty l in
      let args, w = operands args w l in
      let vargs, w = operands vargs w l in
      w, Eset (x, Pcall (l, t, f, args, vargs))
    | `alloc (x, n) -> Eset (x, Palloc (l, n))
    | `load (x, t, a) -> go @@ fun () ->
      let a, w = operand a Worklist.empty l in
      w, Eset (x, Pload (l, t, a))
    | `call (None, f, args, vargs) -> go @@ fun () ->
      let f, w = global f Worklist.empty l in
      let args, w = operands args w l in
      let vargs, w = operands vargs w l in
      w, Ecall (f, args, vargs)
    | `store (t, v, a) -> go @@ fun () ->
      let v, w = operand v Worklist.empty l in
      let a, w = operand a w l in
      w, Estore (t, v, a)
    | `vaarg (x, t, y) -> Evaarg (x, t, y)
    | `vastart x -> Evastart x
end

let try_ f = try f () with
  | Occurs_failed (x, None) ->
    E.failf "Occurs check failed for variable %a" Var.pp x ()
  | Occurs_failed (x, Some l) ->
    E.failf "Occurs check failed for variable %a at instruction %a"
      Var.pp x Label.pp l ()

let build ctx l = try_ @@ fun () ->
  match Hashtbl.find ctx.exp l with
  | Some e -> Ok e
  | None -> match resolve ctx l with
    | Some `blk b -> Ok (Builder.of_ctrl ctx b)
    | Some `insn (i, b) -> Ok (Builder.of_insn ctx i b)
    | None -> E.failf "Label %a not found" Label.pp l ()

let fill ctx = try_ @@ fun () ->
  Map.iter ctx.blks ~f:(fun b ->
      if not @@ Hashtbl.mem ctx.exp @@ Blk.label b then
        ignore @@ Builder.of_ctrl ctx b);
  Map.iter ctx.insns ~f:(fun (i, b) ->
      if not @@ Hashtbl.mem ctx.exp @@ Insn.label i then
        ignore @@ Builder.of_insn ctx i b);
  Ok ()
