open Core
open Context.Syntax

let rules =
  let open Egraph.Enode in
  let open Egraph.Rule in
  let i8  s = exp (Oint (Bv.of_string s,  `i8)) in
  let i16 s = exp (Oint (Bv.of_string s, `i16)) in
  let i32 s = exp (Oint (Bv.of_string s, `i32)) in
  let i64 s = exp (Oint (Bv.of_string s, `i64)) in
  let x = var "x" in
  let y = var "y" in [
    (* Unconditional branch. *)
    (Obr & [exp (Obool  true); x; y]) => (Ojmp & [x]);
    (Obr & [exp (Obool false); x; y]) => (Ojmp & [y]);
    (* Branch to same destination. *)
    (Obr & [x; y; y]) => (Ojmp & [y]);
    (* Unconditional move. *)
    (Osel  `i8 & [exp (Obool  true); x; y]) => (Ounop (`copy  `i8) & [x]);
    (Osel `i16 & [exp (Obool  true); x; y]) => (Ounop (`copy `i16) & [x]);
    (Osel `i32 & [exp (Obool  true); x; y]) => (Ounop (`copy `i32) & [x]);
    (Osel `i64 & [exp (Obool  true); x; y]) => (Ounop (`copy `i64) & [x]);
    (Osel `f32 & [exp (Obool  true); x; y]) => (Ounop (`copy `f32) & [x]);
    (Osel `f64 & [exp (Obool  true); x; y]) => (Ounop (`copy `f64) & [x]);
    (Osel  `i8 & [exp (Obool false); x; y]) => (Ounop (`copy  `i8) & [y]);
    (Osel `i16 & [exp (Obool false); x; y]) => (Ounop (`copy `i16) & [y]);
    (Osel `i32 & [exp (Obool false); x; y]) => (Ounop (`copy `i32) & [y]);
    (Osel `i64 & [exp (Obool false); x; y]) => (Ounop (`copy `i64) & [y]);
    (Osel `f32 & [exp (Obool false); x; y]) => (Ounop (`copy `f32) & [y]);
    (Osel `f64 & [exp (Obool false); x; y]) => (Ounop (`copy `f64) & [y]);
    (* Useless condition. *)
    (Osel  `i8 & [x; y; y]) => (Ounop (`copy  `i8) & [y]);
    (Osel `i16 & [x; y; y]) => (Ounop (`copy `i16) & [y]);
    (Osel `i32 & [x; y; y]) => (Ounop (`copy `i32) & [y]);
    (Osel `i64 & [x; y; y]) => (Ounop (`copy `i64) & [y]);
    (Osel `f32 & [x; y; y]) => (Ounop (`copy `f32) & [y]);
    (Osel `f64 & [x; y; y]) => (Ounop (`copy `f64) & [y]);
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
