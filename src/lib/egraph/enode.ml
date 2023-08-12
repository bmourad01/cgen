open Core
open Virtual

(* Notes:

   - Some ops are just auxilliary to certain other ops.

   - Loads, stores, and calls are marked with either a unique
     variable or a label, in order to prevent them from being
     erroneously hash-consed as equal to some other similarly
     structured node. The reason for this is that these can't
     be safely re-ordered (since they are effectful).
*)
type op =
  | Oaddr     of Bv.t
  | Obinop    of Insn.binop
  | Obool     of bool
  | Obr
  | Ocall0    of Label.t
  | Ocall     of Var.t * Type.basic
  | Ocallargs
  | Odouble   of float
  | Ojmp
  | Oint      of Bv.t * Type.imm
  | Oload     of Var.t * Type.basic
  | Olocal    of Label.t
  | Oret
  | Osel      of Type.basic
  | Oset      of Var.t
  | Osingle   of Float32.t
  | Ostore    of Type.basic * Label.t
  | Osw       of Type.imm
  | Osym      of string * int
  | Otbl      of Bv.t
  | Ounop     of Insn.unop
  | Ovar      of Var.t
[@@deriving compare, equal, hash, sexp]

type t =
  | N of op * Id.t list
  | U of {pre: Id.t; post: Id.t}
[@@deriving compare, equal, hash, sexp]

let is_const = function
  | N (Obool _, [])
  | N (Oint _, [])
  | N (Odouble _, [])
  | N (Osingle _, [])
  | N (Osym _, []) -> true
  | N _ | U _ -> false

let commute = function
  | N (Obinop b, [x; y]) ->
    begin match b with
      | `add _
      | `mul _
      | `mulh _
      | `umulh _
      | `and_ _
      | `or_ _
      | `xor _
      | `eq _
      | `ne _ -> Some (N (Obinop b, [y; x]))
      | _ -> None
    end
  | N _ | U _ -> None

let of_const : const -> t = function
  | `bool b -> N (Obool b, [])
  | `int (i, t) -> N (Oint (i, t), [])
  | `double d -> N (Odouble d, [])
  | `float s -> N (Osingle s, [])
  | `sym (s, o) -> N (Osym (s, o), [])

module Eval = struct
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

  let signed_compare x y m = match Bv.(msb x mod m, msb y mod m) with
    | true,  true  -> Bv.compare y x
    | false, false -> Bv.compare x y
    | true,  false -> -1
    | false, true  -> 1

  (* pre: x is nonzero *)
  let clz x n =
    let i = Bv.to_int64 x in
    let i = match n with
      | (8|16|32|64) -> Int64.(clz (i lsl Int.(64 - n)))
      | _ -> assert false in
    Bv.(int i mod modulus n)

  (* pre: x is nonzero *)
  let ctz x n =
    let i = Bv.to_int64 x in
    let i = match n with
      | (8|16|32|64) -> Int64.ctz i
      | _ -> assert false in
    Bv.(int i mod modulus n)

  let popcnt x n =
    let x = Bv.to_bigint x in
    Bv.(int (Z.popcount x) mod modulus n)

  let imod t = Bv.modulus @@ Type.sizeof_imm t

  let mulh t a b =
    let sz = Type.sizeof_imm t in
    let m = Bv.modulus sz in
    let m2 = Bv.modulus (sz * 2) in
    let sh = Bv.(int sz mod m) in
    Bv.((((a * b) mod m2) asr sh) mod m)

  let umulh t a b =
    let sz = Type.sizeof_imm t in
    let m = Bv.modulus sz in
    let m2 = Bv.modulus (sz * 2) in
    let sh = Bv.(int sz mod m) in
    Bv.((((a * b) mod m2) lsr sh) mod m)

  let rol t a b =
    let sz = Type.sizeof_imm t in
    let m = Bv.modulus sz in
    let sh = Bv.(((int sz mod m) - b) mod m) in
    let lsh = Bv.((a lsl b) mod m) in
    let rsh = Bv.((a lsr sh) mod m) in
    Bv.((lsh lor rsh) mod m)

  let ror t a b =
    let sz = Type.sizeof_imm t in
    let m = Bv.modulus sz in
    let sh = Bv.(((int sz mod m) - b) mod m) in
    let lsh = Bv.((a lsl sh) mod m) in
    let rsh = Bv.((a lsr b) mod m) in
    Bv.((lsh lor rsh) mod m)

  let sext t a ta =
    let sz' = Type.sizeof_imm ta in
    let m' = Bv.modulus sz' in
    if Bv.(msb a mod m') then
      let m = imod t in
      let sh = Bv.(int sz' mod m) in
      Bv.(((((ones mod m) lsl sh) mod m) lor a) mod m)
    else a

  let binop_int o a b = match o with
    | `add (#Type.imm as t) -> Some (`int (Bv.((a + b) mod imod t), t))
    | `div (#Type.imm as t) when Bv.(b <> zero) ->
      Some (`int (Bv.((sdiv a b) mod imod t), t))
    | `mul  (#Type.imm as t) -> Some (`int (Bv.((a * b) mod imod t), t))
    | `mulh (#Type.imm as t) -> Some (`int (mulh t a b, t))
    | `umulh (#Type.imm as t) -> Some (`int (umulh t a b, t))
    | `rem (#Type.imm as t) when Bv.(b <> zero) ->
      Some (`int (Bv.((srem a b) mod imod t), t))
    | `sub (#Type.imm as t) -> Some (`int (Bv.((a - b) mod imod t), t))
    | `udiv t when Bv.(b <> zero) ->
      Some (`int (Bv.((a / b) mod imod t), t))
    | `urem t when Bv.(b <> zero) ->
      Some (`int (Bv.((rem a b) mod imod t), t))
    | `and_ t -> Some (`int (Bv.((a land b) mod imod t), t))
    | `or_  t -> Some (`int (Bv.((a lor  b) mod imod t), t))
    | `asr_ t -> Some (`int (Bv.((a asr  b) mod imod t), t))
    | `lsl_ t -> Some (`int (Bv.((a lsl  b) mod imod t), t))
    | `lsr_ t -> Some (`int (Bv.((a lsr  b) mod imod t), t))
    | `rol t  -> Some (`int (rol t a b, t))
    | `ror t  -> Some (`int (ror t a b, t))
    | `xor t  -> Some (`int (Bv.((a lxor b) mod imod t), t))
    | `eq #Type.imm -> Some (`bool Bv.(a =  b))
    | `ge #Type.imm -> Some (`bool Bv.(a >= b))
    | `gt #Type.imm -> Some (`bool Bv.(a >  b))
    | `le #Type.imm -> Some (`bool Bv.(a <= b))
    | `lt #Type.imm -> Some (`bool Bv.(a <  b))
    | `ne #Type.imm -> Some (`bool Bv.(a <> b))
    | `sge t -> Some (`bool (signed_compare a b (imod t) >= 0))
    | `sgt t -> Some (`bool (signed_compare a b (imod t) >  0))
    | `sle t -> Some (`bool (signed_compare a b (imod t) <= 0))
    | `slt t -> Some (`bool (signed_compare a b (imod t) <  0))
    | _ -> None

  let binop_single o a b = match o with
    | `add `f32 -> Some (`float Float32.(a + b))
    | `div `f32 -> Some (`float Float32.(a / b))
    | `mul `f32 -> Some (`float Float32.(a * b))
    | `rem `f32 -> Some (`float Float32.(rem a b))
    | `sub `f32 -> Some (`float Float32.(a - b))
    | `eq  `f32 -> Some (`bool  Float32.(a = b))
    | `ge  `f32 -> Some (`bool  Float32.(a >= b))
    | `gt  `f32 -> Some (`bool  Float32.(a > b))
    | `le  `f32 -> Some (`bool  Float32.(a <= b))
    | `lt  `f32 -> Some (`bool  Float32.(a < b))
    | `ne  `f32 -> Some (`bool  Float32.(a <> b))
    | `o   `f32 -> Some (`bool  Float32.(is_ordered a b))
    | `uo  `f32 -> Some (`bool  Float32.(is_unordered a b))
    | _ -> None

  let binop_double o a b = match o with
    | `add `f64 -> Some (`double Float.(a + b))
    | `div `f64 -> Some (`double Float.(a / b))
    | `mul `f64 -> Some (`double Float.(a * b))
    | `rem `f64 -> Some (`double Float.(a % b))
    | `sub `f64 -> Some (`double Float.(a - b))
    | `eq  `f64 -> Some (`bool   Float.(a = b))
    | `ge  `f64 -> Some (`bool   Float.(a >= b))
    | `gt  `f64 -> Some (`bool   Float.(a > b))
    | `le  `f64 -> Some (`bool   Float.(a <= b))
    | `lt  `f64 -> Some (`bool   Float.(a < b))
    | `ne  `f64 -> Some (`bool   Float.(a <> b))
    | `o   `f64 -> Some (`bool   (float_ordered a b))
    | `uo  `f64 -> Some (`bool   (float_unordered a b))
    | _ -> None

  let unop_int o a ty = match (o : Insn.unop) with
    | `neg (#Type.imm as t) ->
      Some (`int (Bv.(neg a mod imod t), t))
    | `clz t when Bv.(a <> zero) ->
      Some (`int (clz a @@ Type.sizeof_imm t, t))
    | `ctz t when Bv.(a <> zero) ->
      Some (`int (ctz a @@ Type.sizeof_imm t, t))
    | `not_ t ->
      Some (`int (Bv.(lnot a mod imod t), t))
    | `popcnt t ->
      Some (`int (popcnt a @@ Type.sizeof_imm t, t))
    | `fibits `f32 ->
      Some (`float (Float32.of_bits @@ Bv.to_int32 a))
    | `fibits `f64 ->
      Some (`double (float_of_bits @@ Bv.to_int64 a))
    | `itrunc t when Type.equal_imm t ty -> Some (`int (a, t))
    | `itrunc t ->
      let hi = Type.sizeof_imm t - 1 in
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

  let go op args = match op, args with
    | Oaddr _, _ -> None
    | Obinop o, [Some `int (a, _); Some `int (b, _)] -> binop_int o a b
    | Obinop o, [Some `float a; Some `float b] -> binop_single o a b
    | Obinop o, [Some `double a; Some `double b] -> binop_double o a b
    | Obinop _, _ -> None
    | Obool b, [] -> Some (`bool b)
    | Obool _, _ -> None
    | Obr, _ -> None
    | Ocall0 _, _ -> None
    | Ocall _, _ -> None
    | Ocallargs, _ -> None
    | Odouble d, [] -> Some (`double d)
    | Odouble _, _ -> None
    | Ojmp, _ -> None
    | Oint (i, t), [] -> Some (`int (i, t))
    | Oint _, _ -> None
    | Oload _, _ -> None
    | Olocal _, _ -> None
    | Oret, _ -> None
    | Oset _, _ -> None
    | Osel _, [Some `bool true;  t; _] -> t
    | Osel _, [Some `bool false; _; f] -> f
    | Osel _, _ -> None
    | Osingle s, [] -> Some (`float s)
    | Osingle _, _ -> None
    | Ostore _, _ -> None
    | Osw _, _ -> None
    | Osym (s, o), [] -> Some (`sym (s, o))
    | Osym _, _ -> None
    | Otbl _, _ -> None
    | Ounop o, [Some `int (a, ty)] -> unop_int o a ty
    | Ounop o, [Some `float a] -> unop_single o a
    | Ounop o, [Some `double a] -> unop_double o a
    | Ounop `flag t, [Some `bool b] -> Some (`int (Bv.bool b, t))
    | Ounop _, _ -> None
    | Ovar _, _ -> None
end

let rec const ~node n : const option = match n with
  | N (Obool b, []) -> Some (`bool b)
  | N (Oint (i, t), []) -> Some (`int (i, t))
  | N (Odouble d, []) -> Some (`double d)
  | N (Osingle s, []) -> Some (`float s)
  | N (Osym (s, o), []) -> Some (`sym (s, o))
  | N _ -> None
  | U {pre; post} ->
    let a = const ~node @@ node pre in
    let b = const ~node @@ node post in
    Option.merge a b ~f:(fun a b ->
        assert (equal_const a b);
        a)

let rec eval ~node n : const option = match n with
  | N (op, children) ->
    let cs = List.map children ~f:(fun c ->
        const ~node @@ node c) in
    Eval.go op cs
  | U {pre; post} ->
    let a = eval ~node @@ node pre in
    let b = eval ~node @@ node post in
    Option.merge a b ~f:(fun a b ->
        assert (equal_const a b);
        a)

let pp_op ppf = function
  | Oaddr a ->
    Format.fprintf ppf "(addr %a)" Bv.pp a
  | Obinop b ->
    Format.fprintf ppf "%a" Insn.pp_binop b
  | Obool b ->
    Format.fprintf ppf "%a" Bool.pp b
  | Obr ->
    Format.fprintf ppf "br"
  | Ocall0 _ ->
    Format.fprintf ppf "call"
  | Ocall (_, t) ->
    Format.fprintf ppf "call.%a" Type.pp_basic t
  | Ocallargs ->
    Format.fprintf ppf "callargs"
  | Odouble d ->
    Format.fprintf ppf "%a_d" Float.pp d
  | Ojmp ->
    Format.fprintf ppf "jmp"
  | Oint (i, t) ->
    Format.fprintf ppf "%a_%a" Bv.pp i Type.pp_imm t
  | Oload (x, t) ->
    Format.fprintf ppf "(ld.%a %a)" Type.pp_basic t Var.pp x
  | Olocal l ->
    Format.fprintf ppf "%a" Label.pp l
  | Oret ->
    Format.fprintf ppf "ret"
  | Osel t ->
    Format.fprintf ppf "sel.%a" Type.pp_basic t
  | Oset x ->
    Format.fprintf ppf "(set %a)" Var.pp x
  | Osingle s ->
    Format.fprintf ppf "%s_s" @@ Float32.to_string s
  | Ostore (t, _) ->
    Format.fprintf ppf "st.%a" Type.pp_basic t
  | Osw t ->
    Format.fprintf ppf "sw.%a" Type.pp_imm t
  | Osym (s, 0) ->
    Format.fprintf ppf "$%s" s
  | Osym (s, o) when o > 0 ->
    Format.fprintf ppf "$%s+%d" s o
  | Osym (s, o) ->
    Format.fprintf ppf "$%s-%d" s (lnot o + 1)
  | Otbl i ->
    Format.fprintf ppf "(tbl %a)" Bv.pp i
  | Ounop u ->
    Format.fprintf ppf "%a" Insn.pp_unop u
  | Ovar x ->
    Format.fprintf ppf "%a" Var.pp x

let pp ppf = function
  | N (op, []) -> Format.fprintf ppf "%a" pp_op op
  | N (op, cs) ->
    let pp_sep ppf () = Format.fprintf ppf " " in
    Format.fprintf ppf "(%a %a)" pp_op op
      (Format.pp_print_list ~pp_sep Id.pp) cs
  | U {pre; post} ->
    Format.fprintf ppf "(union %a %a)" Id.pp pre Id.pp post
