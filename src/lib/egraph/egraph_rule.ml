open Egraph_common

type t = rule

let wild = W
let var x = V x
let exp o = P (o, [])
let (&) o q = P (o, q)
let (=>) pre post = {pre; post = Static post; subsume = false}
let (=>?) pre post ~if_ = {pre; post = Cond (post, if_); subsume = false}
let (=>*) pre gen = {pre; post = Dyn gen; subsume = false}
let (=>!) pre post = {pre; post = Static post; subsume = true}
let (=>?!) pre post ~if_ = {pre; post = Cond (post, if_); subsume = true}
let (=>*!) pre gen = {pre; post = Dyn gen; subsume = true}

module Op = struct
  let bop b l r = Obinop b & [l; r]
  let bool b = exp (Obool b)
  let br c y n = Obr & [c; y; n]
  let double d = exp (Odouble d)
  let int i t = exp (Oint (i, t))
  let i8 n = int Bv.(int n mod m8) `i8
  let i16 n = int Bv.(int n mod m16) `i16
  let i32 n = int Bv.(int32 n mod m32) `i32
  let i64 n = int Bv.(int64 n mod m64) `i64
  let jmp d = Ojmp & [d]
  let sel t c y n = Osel t & [c; y; n]
  let single s = exp (Osingle s)
  let sym s o = exp (Osym (s, o))
  let uop u x = Ounop u & [x]
  let ref x = Oref & [x]
  let unref x = Ounref & [wild; x]

  let add     t = bop (`add t)
  let div     t = bop (`div t)
  let mul     t = bop (`mul t)
  let mulh    t = bop (`mulh t)
  let rem     t = bop (`rem t)
  let sub     t = bop (`sub t)
  let udiv    t = bop (`udiv t)
  let umulh   t = bop (`umulh t)
  let urem    t = bop (`urem t)
  let and_    t = bop (`and_ t)
  let or_     t = bop (`or_ t)
  let asr_    t = bop (`asr_ t)
  let lsl_    t = bop (`lsl_ t)
  let lsr_    t = bop (`lsr_ t)
  let rol     t = bop (`rol t)
  let ror     t = bop (`ror t)
  let xor     t = bop (`xor t)
  let neg     t = uop (`neg t)
  let clz     t = uop (`clz t)
  let ctz     t = uop (`ctz t)
  let not_    t = uop (`not_ t)
  let popcnt  t = uop (`popcnt t)
  let eq      t = bop (`eq t)
  let ge      t = bop (`ge t)
  let gt      t = bop (`gt t)
  let le      t = bop (`le t)
  let lt      t = bop (`lt t)
  let ne      t = bop (`ne t)
  let o       t = bop (`o t)
  let sge     t = bop (`sge t)
  let sgt     t = bop (`sgt t)
  let sle     t = bop (`sle t)
  let slt     t = bop (`slt t)
  let uo      t = bop (`uo t)
  let fext    t = uop (`fext t)
  let fibits  t = uop (`fibits t)
  let flag    t = uop (`flag t)
  let ftosi f i = uop (`ftosi (f, i))
  let ftoui f i = uop (`ftoui (f, i))
  let ftrunc  t = uop (`ftrunc t)
  let ifbits  t = uop (`ifbits t)
  let itrunc  t = uop (`itrunc t)
  let sext    t = uop (`sext t)
  let sitof i f = uop (`sitof (i, f))
  let uitof i f = uop (`uitof (i, f))
  let zext    t = uop (`zext t)
  let copy    t = uop (`copy t)
end
