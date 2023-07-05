open Core
open Monads.Std
open Context.Syntax

module O = Monad.Option

let mul_imm_pow2 x y eg _ env =
  let open O.Syntax in
  Map.find env y >>= Egraph.data eg >>= function
  | `int (i, ty) ->
    let i = Bv.to_int64 i in
    if Int64.is_pow2 i then
      let open Egraph.Enode in
      let open Egraph.Rule in
      let m = Bv.modulus @@ Type.sizeof_imm ty in
      let i = exp (Oint (Bv.(int (Int64.ctz i) mod m), ty)) in
      !!(Obinop (`lsl_ ty) & [x; i])
    else None
  | _ -> None

let rules =
  let open Egraph.Enode in
  let open Egraph.Rule in
  let i8  s = exp (Oint (Bv.of_string s,  `i8)) in
  let i16 s = exp (Oint (Bv.of_string s, `i16)) in
  let i32 s = exp (Oint (Bv.of_string s, `i32)) in
  let i64 s = exp (Oint (Bv.of_string s, `i64)) in
  let x = var "x" in
  let y = var "y" in [
    (* x + 0 = x. *)
    (Obinop (`add  `i8) & [x;  i8 "0"]) => x;
    (Obinop (`add `i16) & [x; i16 "0"]) => x;
    (Obinop (`add `i32) & [x; i32 "0"]) => x;
    (Obinop (`add `i64) & [x; i64 "0"]) => x;
    (* x - 0 = x. *)
    (Obinop (`sub  `i8) & [x;  i8 "0"]) => x;
    (Obinop (`sub `i16) & [x; i16 "0"]) => x;
    (Obinop (`sub `i32) & [x; i32 "0"]) => x;
    (Obinop (`sub `i64) & [x; i64 "0"]) => x;
    (* x - x = 0. *)
    (Obinop (`sub  `i8) & [x; x]) =>  i8 "0";
    (Obinop (`sub `i16) & [x; x]) => i16 "0";
    (Obinop (`sub `i32) & [x; x]) => i32 "0";
    (Obinop (`sub `i64) & [x; x]) => i64 "0";
    (* x * 0 = 0. *)
    (Obinop (`mul  `i8) & [x;  i8 "0"]) =>  i8 "0";
    (Obinop (`mul `i16) & [x; i16 "0"]) => i16 "0";
    (Obinop (`mul `i32) & [x; i32 "0"]) => i32 "0";
    (Obinop (`mul `i64) & [x; i64 "0"]) => i64 "0";
    (* x * 1 = x *)
    (Obinop (`mul  `i8) & [x;  i8 "1"]) => x;
    (Obinop (`mul `i16) & [x; i16 "1"]) => x;
    (Obinop (`mul `i32) & [x; i32 "1"]) => x;
    (Obinop (`mul `i64) & [x; i64 "1"]) => x;
    (* x * 2 = 2 * x *)
    (Obinop (`mul  `i8) & [x;  i8 "2"]) => (Obinop (`mul  `i8) & [ i8 "2"; x]);
    (Obinop (`mul `i16) & [x; i16 "2"]) => (Obinop (`mul `i16) & [i16 "2"; x]);
    (Obinop (`mul `i32) & [x; i32 "2"]) => (Obinop (`mul `i32) & [i32 "2"; x]);
    (Obinop (`mul `i64) & [x; i64 "2"]) => (Obinop (`mul `i64) & [i64 "2"; x]);
    (* 2 * x = x + x *)
    (Obinop (`mul  `i8) & [ i8 "2"; x]) => (Obinop (`add  `i8) & [x; x]);
    (Obinop (`mul `i16) & [i16 "2"; x]) => (Obinop (`add `i16) & [x; x]);
    (Obinop (`mul `i32) & [i32 "2"; x]) => (Obinop (`add `i32) & [x; x]);
    (Obinop (`mul `i64) & [i64 "2"; x]) => (Obinop (`add `i64) & [x; x]);
    (* x * c = x << log2(c) when c is power of two *)
    (Obinop (`mul  `i8) & [x; y]) =>* mul_imm_pow2 x "y";
    (Obinop (`mul `i16) & [x; y]) =>* mul_imm_pow2 x "y";
    (Obinop (`mul `i32) & [x; y]) =>* mul_imm_pow2 x "y";
    (Obinop (`mul `i64) & [x; y]) =>* mul_imm_pow2 x "y";
    (* x / 1 = x *)
    (Obinop (`div   `i8) & [x;  i8 "1"]) => x;
    (Obinop (`div  `i16) & [x; i16 "1"]) => x;
    (Obinop (`div  `i32) & [x; i32 "1"]) => x;
    (Obinop (`div  `i64) & [x; i64 "1"]) => x;
    (Obinop (`udiv  `i8) & [x;  i8 "1"]) => x;
    (Obinop (`udiv `i16) & [x; i16 "1"]) => x;
    (Obinop (`udiv `i32) & [x; i32 "1"]) => x;
    (Obinop (`udiv `i64) & [x; i64 "1"]) => x;
    (* x % 1 = 0 *)
    (Obinop (`rem   `i8) & [x;  i8 "1"]) =>  i8 "0";
    (Obinop (`rem  `i16) & [x; i16 "1"]) => i16 "0";
    (Obinop (`rem  `i32) & [x; i32 "1"]) => i32 "0";
    (Obinop (`rem  `i64) & [x; i64 "1"]) => i64 "0";
    (Obinop (`urem  `i8) & [x;  i8 "1"]) =>  i8 "0";
    (Obinop (`urem `i16) & [x; i16 "1"]) => i16 "0";
    (Obinop (`urem `i32) & [x; i32 "1"]) => i32 "0";
    (Obinop (`urem `i64) & [x; i64 "1"]) => i64 "0";
    (* br true, x, y = jmp x *)
    (Obr & [exp (Obool  true); x; y]) => (Ojmp & [x]);
    (* br false, x, y = jmp y *)
    (Obr & [exp (Obool false); x; y]) => (Ojmp & [y]);
    (* br x, y, y = jmp y. *)
    (Obr & [x; y; y]) => (Ojmp & [y]);
    (* true ? x : y = x. *)
    (Osel  `i8 & [exp (Obool  true); x; y]) => (Ounop (`copy  `i8) & [x]);
    (Osel `i16 & [exp (Obool  true); x; y]) => (Ounop (`copy `i16) & [x]);
    (Osel `i32 & [exp (Obool  true); x; y]) => (Ounop (`copy `i32) & [x]);
    (Osel `i64 & [exp (Obool  true); x; y]) => (Ounop (`copy `i64) & [x]);
    (Osel `f32 & [exp (Obool  true); x; y]) => (Ounop (`copy `f32) & [x]);
    (Osel `f64 & [exp (Obool  true); x; y]) => (Ounop (`copy `f64) & [x]);
    (* false ? x : y = y *)
    (Osel  `i8 & [exp (Obool false); x; y]) => (Ounop (`copy  `i8) & [y]);
    (Osel `i16 & [exp (Obool false); x; y]) => (Ounop (`copy `i16) & [y]);
    (Osel `i32 & [exp (Obool false); x; y]) => (Ounop (`copy `i32) & [y]);
    (Osel `i64 & [exp (Obool false); x; y]) => (Ounop (`copy `i64) & [y]);
    (Osel `f32 & [exp (Obool false); x; y]) => (Ounop (`copy `f32) & [y]);
    (Osel `f64 & [exp (Obool false); x; y]) => (Ounop (`copy `f64) & [y]);
    (* x ? y : y = y. *)
    (Osel  `i8 & [x; y; y]) => y;
    (Osel `i16 & [x; y; y]) => y;
    (Osel `i32 & [x; y; y]) => y;
    (Osel `i64 & [x; y; y]) => y;
    (Osel `f32 & [x; y; y]) => y;
    (Osel `f64 & [x; y; y]) => y;
    (* Specialize to `flag`. *)
    (Osel  `i8 & [x;  i8 "1";  i8 "0"]) => (Ounop (`flag  `i8) & [x]);
    (Osel `i16 & [x; i16 "1"; i16 "0"]) => (Ounop (`flag `i16) & [x]);
    (Osel `i32 & [x; i32 "1"; i32 "0"]) => (Ounop (`flag `i32) & [x]);
    (Osel `i64 & [x; i64 "1"; i64 "0"]) => (Ounop (`flag `i64) & [x]);
    (Osel  `i8 & [x;  i8 "0";  i8 "1"]) => (Obinop (`xor  `i8) & [Ounop (`flag `i8)  & [x];  i8 "1"]);
    (Osel `i16 & [x; i16 "0"; i16 "1"]) => (Obinop (`xor `i16) & [Ounop (`flag `i16) & [x]; i16 "1"]);
    (Osel `i32 & [x; i32 "0"; i32 "1"]) => (Obinop (`xor `i32) & [Ounop (`flag `i32) & [x]; i32 "1"]);
    (Osel `i64 & [x; i64 "0"; i64 "1"]) => (Obinop (`xor `i64) & [Ounop (`flag `i64) & [x]; i64 "1"]);
    (* Copy propagation. *)
    (Ounop (`copy  `i8) & [x]) => x;
    (Ounop (`copy `i16) & [x]) => x;
    (Ounop (`copy `i32) & [x]) => x;
    (Ounop (`copy `i64) & [x]) => x;
    (Ounop (`copy `f32) & [x]) => x;
    (Ounop (`copy `f64) & [x]) => x;
  ]  

let cost ~child n =
  let init = match Egraph.Enode.op n with
    | Obool _ | Odouble _ | Oint _ | Osingle _ | Osym _ -> 0
    | Ovar _ -> 1
    | _ -> 2 in
  Egraph.Enode.children n |>
  List.fold ~init ~f:(fun k c -> k + child c)

let run fn =
  let*? eg = Egraph.create fn in
  let _ = Egraph.fixpoint eg rules in
  let ex = Egraph.Extractor.init eg ~cost in
  Egraph.Extractor.reify ex
