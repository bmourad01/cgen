open Core
open Monads.Std
open Context.Syntax
open Virtual

module O = Monad.Option

module Rules = struct
  open Egraph.Rule

  let is_const x eg _ env =
    Map.find env x |>
    Option.bind ~f:(Egraph.data eg) |>
    Option.is_some

  let imod t = Bv.modulus @@ Type.sizeof_imm t

  (* Dynamically rewrite a multiplication by a power of two into
     a left shift. *)
  let mul_imm_pow2 x y eg _ env =
    let open O.Syntax in
    Map.find env y >>= Egraph.data eg >>= function
    | `int (i, ty) ->
      let i = Bv.to_int64 i in
      O.guard Int64.(i <> 0L && (i land pred i) = 0L) >>| fun () ->
      Op.(lsl_ ty x (int Bv.(int (Int64.ctz i) mod imod ty) ty))
    | _ -> None

  (* Dynamically rewrite an unsigned division by a power of two into
     a right shift. *)
  let udiv_imm_pow2 x y eg _ env =
    let open O.Syntax in
    Map.find env y >>= Egraph.data eg >>= function
    | `int (i, ty) ->
      let i = Bv.to_int64 i in
      O.guard Int64.(i <> 0L && (i land pred i) = 0L) >>| fun () ->
      Op.(lsr_ ty x (int Bv.(int (Int64.ctz i) mod imod ty) ty))
    | _ -> None

  (* Dynamically rewrite an unsigned remainder by a power of two into
     a bitwise AND. *)
  let urem_imm_pow2 x y eg _ env =
    let open O.Syntax in
    Map.find env y >>= Egraph.data eg >>= function
    | `int (i, ty) ->
      let i = Bv.to_int64 i in
      let i' = Int64.pred i in
      O.guard Int64.(i <> 0L && (i land i') = 0L) >>| fun () ->
      Op.(and_ ty x (int Bv.(int64 i' mod imod ty) ty))
    | _ -> None

  let x = var "x"
  let y = var "y"
  let z = var "z"

  let is_const_x = is_const "x"
  let is_const_y = is_const "y"

  let mul_imm_pow2_y = mul_imm_pow2 x "y"
  let udiv_imm_pow2_y = udiv_imm_pow2 x "y"
  let urem_imm_pow2_y = urem_imm_pow2 x "y"

  let rules = Op.[
      (* Commutativity of constants. *)
      (add `i8 x y =>? add `i8 y x) ~if_:is_const_x;
      (add `i16 x y =>? add `i16 y x) ~if_:is_const_x;
      (add `i32 x y =>? add `i32 y x) ~if_:is_const_x;
      (add `i64 x y =>? add `i64 y x) ~if_:is_const_x;
      (mul `i8 x y =>? mul `i8 y x) ~if_:is_const_x;
      (mul `i16 x y =>? mul `i16 y x) ~if_:is_const_x;
      (mul `i32 x y =>? mul `i32 y x) ~if_:is_const_x;
      (mul `i64 x y =>? mul `i64 y x) ~if_:is_const_x;
      (mulh `i8 x y =>? mulh `i8 y x) ~if_:is_const_x;
      (mulh `i16 x y =>? mulh `i16 y x) ~if_:is_const_x;
      (mulh `i32 x y =>? mulh `i32 y x) ~if_:is_const_x;
      (mulh `i64 x y =>? mulh `i64 y x) ~if_:is_const_x;
      (and_ `i8 x y =>? and_ `i8 y x) ~if_:is_const_x;
      (and_ `i16 x y =>? and_ `i16 y x) ~if_:is_const_x;
      (and_ `i32 x y =>? and_ `i32 y x) ~if_:is_const_x;
      (and_ `i64 x y =>? and_ `i64 y x) ~if_:is_const_x;
      (or_ `i8 x y =>? or_ `i8 y x) ~if_:is_const_x;
      (or_ `i16 x y =>? or_ `i16 y x) ~if_:is_const_x;
      (or_ `i32 x y =>? or_ `i32 y x) ~if_:is_const_x;
      (or_ `i64 x y =>? or_ `i64 y x) ~if_:is_const_x;
      (xor `i8 x y =>? xor `i8 y x) ~if_:is_const_x;
      (xor `i16 x y =>? xor `i16 y x) ~if_:is_const_x;
      (xor `i32 x y =>? xor `i32 y x) ~if_:is_const_x;
      (xor `i64 x y =>? xor `i64 y x) ~if_:is_const_x;
      (eq `i8 x y =>? eq `i8 y x) ~if_:is_const_x;
      (eq `i16 x y =>? eq `i16 y x) ~if_:is_const_x;
      (eq `i32 x y =>? eq `i32 y x) ~if_:is_const_x;
      (eq `i64 x y =>? eq `i64 y x) ~if_:is_const_x;
      (ne `i8 x y =>? ne `i8 y x) ~if_:is_const_x;
      (ne `i16 x y =>? ne `i16 y x) ~if_:is_const_x;
      (ne `i32 x y =>? ne `i32 y x) ~if_:is_const_x;
      (ne `i64 x y =>? ne `i64 y x) ~if_:is_const_x;
      (gt `i8 x y =>? lt `i8 y x) ~if_:is_const_x;
      (gt `i16 x y =>? lt `i16 y x) ~if_:is_const_x;
      (gt `i32 x y =>? lt `i32 y x) ~if_:is_const_x;
      (gt `i64 x y =>? lt `i64 y x) ~if_:is_const_x;
      (ge `i8 x y =>? le `i8 y x) ~if_:is_const_x;
      (ge `i16 x y =>? le `i16 y x) ~if_:is_const_x;
      (ge `i32 x y =>? le `i32 y x) ~if_:is_const_x;
      (ge `i64 x y =>? le `i64 y x) ~if_:is_const_x;
      (le `i8 x y =>? ge `i8 y x) ~if_:is_const_x;
      (le `i16 x y =>? ge `i16 y x) ~if_:is_const_x;
      (le `i32 x y =>? ge `i32 y x) ~if_:is_const_x;
      (le `i64 x y =>? ge `i64 y x) ~if_:is_const_x;
      (lt `i8 x y =>? gt `i8 y x) ~if_:is_const_x;
      (lt `i16 x y =>? gt `i16 y x) ~if_:is_const_x;
      (lt `i32 x y =>? gt `i32 y x) ~if_:is_const_x;
      (lt `i64 x y =>? gt `i64 y x) ~if_:is_const_x;
      (sgt `i8 x y =>? slt `i8 y x) ~if_:is_const_x;
      (sgt `i16 x y =>? slt `i16 y x) ~if_:is_const_x;
      (sgt `i32 x y =>? slt `i32 y x) ~if_:is_const_x;
      (sgt `i64 x y =>? slt `i64 y x) ~if_:is_const_x;
      (sge `i8 x y =>? sle `i8 y x) ~if_:is_const_x;
      (sge `i16 x y =>? sle `i16 y x) ~if_:is_const_x;
      (sge `i32 x y =>? sle `i32 y x) ~if_:is_const_x;
      (sge `i64 x y =>? sle `i64 y x) ~if_:is_const_x;
      (sle `i8 x y =>? sge `i8 y x) ~if_:is_const_x;
      (sle `i16 x y =>? sge `i16 y x) ~if_:is_const_x;
      (sle `i32 x y =>? sge `i32 y x) ~if_:is_const_x;
      (sle `i64 x y =>? sge `i64 y x) ~if_:is_const_x;
      (slt `i8 x y =>? sgt `i8 y x) ~if_:is_const_x;
      (slt `i16 x y =>? sgt `i16 y x) ~if_:is_const_x;
      (slt `i32 x y =>? sgt `i32 y x) ~if_:is_const_x;
      (slt `i64 x y =>? sgt `i64 y x) ~if_:is_const_x;
      (* Enable constant folding via associativity. *)
      (add `i8 (add `i8 x y) z =>? add `i8 x (add `i8 z y)) ~if_:is_const_y;
      (add `i16 (add `i16 x y) z =>? add `i16 x (add `i16 z y)) ~if_:is_const_y;
      (add `i32 (add `i32 x y) z =>? add `i32 x (add `i32 z y)) ~if_:is_const_y;
      (add `i64 (add `i64 x y) z =>? add `i64 x (add `i64 z y)) ~if_:is_const_y;
      (mul `i8 (mul `i8 x y) z =>? mul `i8 x (mul `i8 z y)) ~if_:is_const_y;
      (mul `i16 (mul `i16 x y) z =>? mul `i16 x (mul `i16 z y)) ~if_:is_const_y;
      (mul `i32 (mul `i32 x y) z =>? mul `i32 x (mul `i32 z y)) ~if_:is_const_y;
      (mul `i64 (mul `i64 x y) z =>? mul `i64 x (mul `i64 z y)) ~if_:is_const_y;
      (and_ `i8 (and_ `i8 x y) z =>? and_ `i8 x (and_ `i8 z y)) ~if_:is_const_y;
      (and_ `i16 (and_ `i16 x y) z =>? and_ `i16 x (and_ `i16 z y)) ~if_:is_const_y;
      (and_ `i32 (and_ `i32 x y) z =>? and_ `i32 x (and_ `i32 z y)) ~if_:is_const_y;
      (and_ `i64 (and_ `i64 x y) z =>? and_ `i64 x (and_ `i64 z y)) ~if_:is_const_y;
      (or_ `i8 (or_ `i8 x y) z =>? or_ `i8 x (or_ `i8 z y)) ~if_:is_const_y;
      (or_ `i16 (or_ `i16 x y) z =>? or_ `i16 x (or_ `i16 z y)) ~if_:is_const_y;
      (or_ `i32 (or_ `i32 x y) z =>? or_ `i32 x (or_ `i32 z y)) ~if_:is_const_y;
      (or_ `i64 (or_ `i64 x y) z =>? or_ `i64 x (or_ `i64 z y)) ~if_:is_const_y;
      (xor `i8 (xor `i8 x y) z =>? xor `i8 x (xor `i8 z y)) ~if_:is_const_y;
      (xor `i16 (xor `i16 x y) z =>? xor `i16 x (xor `i16 z y)) ~if_:is_const_y;
      (xor `i32 (xor `i32 x y) z =>? xor `i32 x (xor `i32 z y)) ~if_:is_const_y;
      (xor `i64 (xor `i64 x y) z =>? xor `i64 x (xor `i64 z y)) ~if_:is_const_y;
      (sub `i8 (sub `i8 x y) z =>? sub `i8 x (add `i8 z y)) ~if_:is_const_y;
      (sub `i16 (sub `i16 x y) z =>? sub `i16 x (add `i16 z y)) ~if_:is_const_y;
      (sub `i32 (sub `i32 x y) z =>? sub `i32 x (add `i32 z y)) ~if_:is_const_y;
      (sub `i64 (sub `i64 x y) z =>? sub `i64 x (add `i64 z y)) ~if_:is_const_y;
      (sub `i8 (sub `i8 x y) z =>? sub `i8 (sub `i8 x z) y) ~if_:is_const_x;
      (sub `i16 (sub `i16 x y) z =>? sub `i16 (sub `i16 x z) y) ~if_:is_const_x;
      (sub `i32 (sub `i32 x y) z =>? sub `i32 (sub `i32 x z) y) ~if_:is_const_x;
      (sub `i64 (sub `i64 x y) z =>? sub `i64 (sub `i64 x z) y) ~if_:is_const_x;
      (sub `i8 (add `i8 x y) z =>? sub `i8 x (sub `i8 z y)) ~if_:is_const_y;
      (sub `i16 (add `i16 x y) z =>? sub `i16 x (sub `i16 z y)) ~if_:is_const_y;
      (sub `i32 (add `i32 x y) z =>? sub `i32 x (sub `i32 z y)) ~if_:is_const_y;
      (sub `i64 (add `i64 x y) z =>? sub `i64 x (sub `i64 z y)) ~if_:is_const_y;
      (add `i8 (sub `i8 x y) z =>? add `i8 x (sub `i8 z y)) ~if_:is_const_y;
      (add `i16 (sub `i16 x y) z =>? add `i16 x (sub `i16 z y)) ~if_:is_const_y;
      (add `i32 (sub `i32 x y) z =>? add `i32 x (sub `i32 z y)) ~if_:is_const_y;
      (add `i64 (sub `i64 x y) z =>? add `i64 x (sub `i64 z y)) ~if_:is_const_y;
      (add `i8 (sub `i8 x y) z =>? sub `i8 (add `i8 x z) y) ~if_:is_const_x;
      (add `i16 (sub `i16 x y) z =>? sub `i16 (add `i16 x z) y) ~if_:is_const_x;
      (add `i32 (sub `i32 x y) z =>? sub `i32 (add `i32 x z) y) ~if_:is_const_x;
      (add `i64 (sub `i64 x y) z =>? sub `i64 (add `i64 x z) y) ~if_:is_const_x;
      (* x + 0 = x. *)
      add `i8 x  (i8 0) => x;
      add `i16 x (i16 0) => x;
      add `i32 x (i32 0l) => x;
      add `i64 x (i64 0L) => x;
      (* x - 0 = x. *)
      sub `i8 x  (i8 0) => x;
      sub `i16 x (i16 0) => x;
      sub `i32 x (i32 0l) => x;
      sub `i64 x (i64 0L) => x;
      (* 0 - x = -x *)
      sub `i8  (i8 0) x => neg `i8 x;
      sub `i16 (i16 0) x => neg `i16 x;
      sub `i32 (i32 0l) x => neg `i32 x;
      sub `i64 (i64 0L) x => neg `i64 x;
      (* -(-x) = x *)
      neg `i8 (neg `i8 x) => x;
      neg `i16 (neg `i16 x) => x;
      neg `i32 (neg `i32 x) => x;
      neg `i64 (neg `i64 x) => x;
      (* ~(~x) = x *)
      not_ `i8 (not_ `i8 x) => x;
      not_ `i16 (not_ `i16 x) => x;
      not_ `i32 (not_ `i32 x) => x;
      not_ `i64 (not_ `i64 x) => x;
      (* ~x + 1 = -x *)
      add `i8 (not_ `i8 x) (i8 1) => neg `i8 x;
      add `i16 (not_ `i16 x) (i16 1) => neg `i16 x;
      add `i32 (not_ `i32 x) (i32 1l) => neg `i32 x;
      add `i64 (not_ `i64 x) (i64 1L) => neg `i64 x;
      (* -x * -y = x * y *)
      mul `i8 (neg `i8 x) (neg `i8 y) => mul `i8 x y;
      mul `i16 (neg `i16 x) (neg `i16 y) => mul `i16 x y;
      mul `i32 (neg `i32 x) (neg `i32 y) => mul `i32 x y;
      mul `i64 (neg `i64 x) (neg `i64 y) => mul `i64 x y;
      (* x - x = 0. *)
      sub `i8 x x =>  i8 0;
      sub `i16 x x => i16 0;
      sub `i32 x x => i32 0l;
      sub `i64 x x => i64 0L;
      (* x * 0 = 0. *)
      mul `i8 x  (i8 0) =>  i8 0;
      mul `i16 x (i16 0) => i16 0;
      mul `i32 x (i32 0l) => i32 0l;
      mul `i64 x (i64 0L) => i64 0L;
      mulh `i8 x  (i8 0) =>  i8 0;
      mulh `i16 x (i16 0) => i16 0;
      mulh `i32 x (i32 0l) => i32 0l;
      mulh `i64 x (i64 0L) => i64 0L;
      (* x * 1 = x *)
      mul `i8 x  (i8 1) => x;
      mul `i16 x (i16 1) => x;
      mul `i32 x (i32 1l) => x;
      mul `i64 x (i64 1L) => x;
      mulh `i8 x  (i8 1) => x;
      mulh `i16 x (i16 1) => x;
      mulh `i32 x (i32 1l) => x;
      mulh `i64 x (i64 1L) => x;
      (* x * -1 = -x *)
      mul `i8 x  (i8 (-1)) => neg `i8 x;
      mul `i16 x (i16 (-1)) => neg `i16 x;
      mul `i32 x (i32 (-1l)) => neg `i32 x;
      mul `i64 x (i64 (-1L)) => neg `i64 x;
      (* x * 2 = x + x *)
      mul `i8  x (i8 2) => add `i8 x x;
      mul `i16 x (i16 2) => add `i16 x x;
      mul `i32 x (i32 2l) => add `i32 x x;
      mul `i64  x(i64 2L) => add `i64 x x;
      (* x * c = x << log2(c) when c is power of two *)
      mul `i8 x y =>* mul_imm_pow2_y;
      mul `i16 x y =>* mul_imm_pow2_y;
      mul `i32 x y =>* mul_imm_pow2_y;
      mul `i64 x y =>* mul_imm_pow2_y;
      (* unsigned x / c = x >> log2(c) when c is power of two *)
      udiv `i8 x y =>* udiv_imm_pow2_y;
      udiv `i16 x y =>* udiv_imm_pow2_y;
      udiv `i32 x y =>* udiv_imm_pow2_y;
      udiv `i64 x y =>* udiv_imm_pow2_y;
      (* unsigned x % c = x & (c - 1) when c is power of two *)
      urem `i8 x y =>* urem_imm_pow2_y;
      urem `i16 x y =>* urem_imm_pow2_y;
      urem `i32 x y =>* urem_imm_pow2_y;
      urem `i64 x y =>* urem_imm_pow2_y;
      (* x / 1 = x *)
      div `i8  x (i8 1) => x;
      div `i16 x (i16 1) => x;
      div `i32 x (i32 1l) => x;
      div `i64 x (i64 1L) => x;
      udiv `i8 x (i8 1) => x;
      udiv `i16 x (i16 1) => x;
      udiv `i32 x (i32 1l) => x;
      udiv `i64 x (i64 1L) => x;
      (* x % 1 = 0 *)
      rem `i8 x (i8 1) => i8 0;
      rem `i16 x (i16 1) => i16 0;
      rem `i32 x (i32 1l) => i32 0l;
      rem `i64 x (i64 1L) => i64 0L;
      urem `i8 x (i8 1) => i8 0;
      urem `i16 x (i16 1) => i16 0;
      urem `i32 x (i32 1l) => i32 0l;
      urem `i64 x (i64 1L) => i64 0L;
      (* x & 0 = 0 *)
      and_ `i8 x (i8 0) => i8 0;
      and_ `i16 x (i16 0) => i16 0;
      and_ `i32 x (i32 0l) => i32 0l;
      and_ `i64 x (i64 0L) => i64 0L;
      (* x & 0xff... = x *)
      and_ `i8 x  (i8 0xff) => x;
      and_ `i16 x (i16 0xffff) => x;
      and_ `i32 x (i32 0xffff_ffffl) => x;
      and_ `i64 x (i64 0xffff_ffff_ffff_ffffL) => x;
      (* x & x = x *)
      and_ `i8 x x => x;
      and_ `i16 x x => x;
      and_ `i32 x x => x;
      and_ `i64 x x => x;
      (* x | 0 = x *)
      or_ `i8 x (i8 0) => x;
      or_ `i16 x (i16 0) => x;
      or_ `i32 x (i32 0l) => x;
      or_ `i64 x (i64 0L) => x;
      (* x | 0xff... = 0xff... *)
      or_ `i8 x (i8 0xff) => i8 0xff;
      or_ `i16 x (i16 0xffff) => i16 0xffff;
      or_ `i32 x (i32 0xffff_ffffl) => i32 0xffff_ffffl;
      or_ `i64 x (i64 0xffff_ffff_ffff_ffffL) => i64 0xffff_ffff_ffff_ffffL;
      (* x | x = x *)
      or_ `i8 x x => x;
      or_ `i16 x x => x;
      or_ `i32 x x => x;
      or_ `i64 x x => x;
      (* x | ~x = 0xff... *)
      or_ `i8 x (not_ `i8 x) => i8 0xff;
      or_ `i16 x (not_ `i16 x) => i16 0xffff;
      or_ `i32 x (not_ `i32 x) => i32 0xffff_ffffl;
      or_ `i64 x (not_ `i64 x) => i64 0xffff_ffff_ffff_ffffL;
      (* ~x | x = 0xff... *)
      or_ `i8 (not_ `i8 x) x => i8 0xff;
      or_ `i16 (not_ `i16 x) x => i16 0xffff;
      or_ `i32 (not_ `i32 x) x => i32 0xffff_ffffl;
      or_ `i64 (not_ `i64 x) x => i64 0xffff_ffff_ffff_ffffL;
      (* ~(x | y) = ~x & ~y *)
      not_ `i8 (or_ `i8 x y) => and_ `i8 (not_ `i8 x) (not_ `i8 y);
      not_ `i16 (or_ `i16 x y) => and_ `i16 (not_ `i16 x) (not_ `i16 y);
      not_ `i32 (or_ `i32 x y) => and_ `i32 (not_ `i32 x) (not_ `i32 y);
      not_ `i64 (or_ `i64 x y) => and_ `i64 (not_ `i64 x) (not_ `i64 y);
      (* ~(x & y) = ~x | ~y *)
      not_ `i8 (and_ `i8 x y) => or_ `i8 (not_ `i8 x) (not_ `i8 y);
      not_ `i16 (and_ `i16 x y) => or_ `i16 (not_ `i16 x) (not_ `i16 y);
      not_ `i32 (and_ `i32 x y) => or_ `i32 (not_ `i32 x) (not_ `i32 y);
      not_ `i64 (and_ `i64 x y) => or_ `i64 (not_ `i64 x) (not_ `i64 y);
      (* (x & y) | ~y = x | ~y *)
      or_ `i8 (and_ `i8 x y) (not_ `i8 y) => or_ `i8 x (not_ `i8 y);
      or_ `i16 (and_ `i16 x y) (not_ `i16 y) => or_ `i16 x (not_ `i16 y);
      or_ `i32 (and_ `i32 x y) (not_ `i32 y) => or_ `i32 x (not_ `i32 y);
      or_ `i64 (and_ `i64 x y) (not_ `i64 y) => or_ `i64 x (not_ `i64 y);
      (* ~y | (x & y) => x | ~y *)
      or_ `i8 (not_ `i8 y) (and_ `i8 x y) => or_ `i8 x (not_ `i8 y);
      or_ `i16 (not_ `i16 y) (and_ `i16 x y) => or_ `i16 x (not_ `i16 y);
      or_ `i32 (not_ `i32 y) (and_ `i32 x y) => or_ `i32 x (not_ `i32 y);
      or_ `i64 (not_ `i64 y) (and_ `i64 x y) => or_ `i64 x (not_ `i64 y);
      (* x >>> 0 = x *)
      asr_ `i8 x (i8 0) => x;
      asr_ `i16 x (i16 0) => x;
      asr_ `i32 x (i32 0l) => x;
      asr_ `i64 x (i64 0L) => x;
      (* x << 0 = x *)
      lsl_ `i8 x (i8 0) => x;
      lsl_ `i16 x (i16 0) => x;
      lsl_ `i32 x (i32 0l) => x;
      lsl_ `i64 x (i64 0L) => x;
      (* x >> 0 = x *)
      lsr_ `i8 x (i8 0) => x;
      lsr_ `i16 x (i16 0) => x;
      lsr_ `i32 x (i32 0l) => x;
      lsr_ `i64 x (i64 0L) => x;
      (* rol x 0 = x *)
      rol `i8 x (i8 0) => x;
      rol `i16 x (i16 0) => x;
      rol `i32 x (i32 0l) => x;
      rol `i64 x (i64 0L) => x;
      (* ror x 0 = x *)
      ror `i8 x (i8 0) => x;
      ror `i16 x (i16 0) => x;
      ror `i32 x (i32 0l) => x;
      ror `i64 x (i64 0L) => x;
      (* x ^ 0 = x *)
      xor `i8 x (i8 0) => x;
      xor `i16 x (i16 0) => x;
      xor `i32 x (i32 0l) => x;
      xor `i64 x (i64 0L) => x;
      (* x ^ 0xff... = ~x *)
      xor `i8 x (i8 0xff) => not_ `i8 x;
      xor `i16 x (i16 0xffff) => not_ `i16 x;
      xor `i32 x (i32 0xffff_ffffl) => not_ `i32 x;
      xor `i64 x (i64 0xffff_ffff_ffff_ffffL) => not_ `i64 x;
      (* x ^ x = 0 *)
      xor `i8 x x => i8 0;
      xor `i16 x x => i16 0;
      xor `i32 x x => i32 0l;
      xor `i64 x x => i64 0L;
      (* x ^ ~x = 0xff... *)
      xor `i8 x (not_ `i8 x) => i8 0xff;
      xor `i16 x (not_ `i16 x) => i16 0xffff;
      xor `i32 x (not_ `i32 x) => i32 0xffff_ffffl;
      xor `i64 x (not_ `i64 x) => i64 0xffff_ffff_ffff_ffffL;
      (* ~x ^ x = 0xff... *)
      xor `i8 (not_ `i8 x) x => i8 0xff;
      xor `i16 (not_ `i16 x) x => i16 0xffff;
      xor `i32 (not_ `i32 x) x => i32 0xffff_ffffl;
      xor `i64 (not_ `i64 x) x => i64 0xffff_ffff_ffff_ffffL;
      (* x == x = true *)
      eq `i8 x x => bool true;
      eq `i16 x x => bool true;
      eq `i32 x x => bool true;
      eq `i64 x x => bool true;
      (* x != x = false *)
      ne `i8 x x => bool false;
      ne `i16 x x => bool false;
      ne `i32 x x => bool false;
      ne `i64 x x => bool false;
      (* x >= x = true *)
      ge `i8 x x => bool true;
      ge `i16 x x => bool true;
      ge `i32 x x => bool true;
      ge `i64 x x => bool true;
      sge `i8 x x => bool true;
      sge `i16 x x => bool true;
      sge `i32 x x => bool true;
      sge `i64 x x => bool true;
      (* x > x = false *)
      gt `i8 x x => bool false;
      gt `i16 x x => bool false;
      gt `i32 x x => bool false;
      gt `i64 x x => bool false;
      sgt `i8 x x => bool false;
      sgt `i16 x x => bool false;
      sgt `i32 x x => bool false;
      sgt `i64 x x => bool false;
      (* x <= x = true *)
      le `i8 x x => bool true;
      le `i16 x x => bool true;
      le `i32 x x => bool true;
      le `i64 x x => bool true;
      sle `i8 x x => bool true;
      sle `i16 x x => bool true;
      sle `i32 x x => bool true;
      sle `i64 x x => bool true;
      (* x < x = false *)
      lt `i8 x x => bool false;
      lt `i16 x x => bool false;
      lt `i32 x x => bool false;
      lt `i64 x x => bool false;
      slt `i8 x x => bool false;
      slt `i16 x x => bool false;
      slt `i32 x x => bool false;
      slt `i64 x x => bool false;
      (* flag (x == y) ^ 1 => flag (x != y) *)
      xor `i8 (flag `i8 (eq `i8 x y)) (i8 1) => flag `i8 (ne `i8 x y);
      xor `i16 (flag `i16 (eq `i16 x y)) (i16 1) => flag `i16 (ne `i16 x y);
      xor `i32 (flag `i32 (eq `i32 x y)) (i32 1l) => flag `i32 (ne `i32 x y);
      xor `i64 (flag `i64 (eq `i64 x y)) (i64 1L) => flag `i64 (ne `i64 x y);
      (* flag (x != y) ^ 1 => x == y *)
      xor `i8 (flag `i8 (ne `i8 x y)) (i8 1) => flag `i8 (eq `i8 x y);
      xor `i16 (flag `i16 (ne `i16 x y)) (i16 1) => flag `i16 (eq `i16 x y);
      xor `i32 (flag `i32 (ne `i32 x y)) (i32 1l) => flag `i32 (eq `i32 x y);
      xor `i64 (flag `i64 (ne `i64 x y)) (i64 1L) => flag `i64 (eq `i64 x y);
      (* flag (x >= y) ^ 1 => x < y *)
      xor `i8 (flag `i8 (ge `i8 x y)) (i8 1) => flag `i8 (lt `i8 x y);
      xor `i16 (flag `i16 (ge `i16 x y)) (i16 1) => flag `i16 (lt `i16 x y);
      xor `i32 (flag `i32 (ge `i32 x y)) (i32 1l) => flag `i32 (lt `i32 x y);
      xor `i64 (flag `i64 (ge `i64 x y)) (i64 1L) => flag `i64 (lt `i64 x y);
      xor `i8 (flag `i8 (sge `i8 x y)) (i8 1) => flag `i8 (slt `i8 x y);
      xor `i16 (flag `i16 (sge `i16 x y)) (i16 1) => flag `i16 (slt `i16 x y);
      xor `i32 (flag `i32 (sge `i32 x y)) (i32 1l) => flag `i32 (slt `i32 x y);
      xor `i64 (flag `i64 (sge `i64 x y)) (i64 1L) => flag `i64 (slt `i64 x y);
      (* flag (x > y) ^ 1 => x <= y *)
      xor `i8 (flag `i8 (gt `i8 x y)) (i8 1) => flag `i8 (le `i8 x y);
      xor `i16 (flag `i16 (gt `i16 x y)) (i16 1) => flag `i16 (le `i16 x y);
      xor `i32 (flag `i32 (gt `i32 x y)) (i32 1l) => flag `i32 (le `i32 x y);
      xor `i64 (flag `i64 (gt `i64 x y)) (i64 1L) => flag `i64 (le `i64 x y);
      xor `i8 (flag `i8 (sgt `i8 x y)) (i8 1) => flag `i8 (sle `i8 x y);
      xor `i16 (flag `i16 (sgt `i16 x y)) (i16 1) => flag `i16 (sle `i16 x y);
      xor `i32 (flag `i32 (sgt `i32 x y)) (i32 1l) => flag `i32 (sle `i32 x y);
      xor `i64 (flag `i64 (sgt `i64 x y)) (i64 1L) => flag `i64 (sle `i64 x y);
      (* flag (x <= y) ^ 1 => x > y *)
      xor `i8 (flag `i8 (le `i8 x y)) (i8 1) => flag `i8 (gt `i8 x y);
      xor `i16 (flag `i16 (le `i16 x y)) (i16 1) => flag `i16 (gt `i16 x y);
      xor `i32 (flag `i32 (le `i32 x y)) (i32 1l) => flag `i32 (gt `i32 x y);
      xor `i64 (flag `i64 (le `i64 x y)) (i64 1L) => flag `i64 (gt `i64 x y);
      xor `i8 (flag `i8 (sle `i8 x y)) (i8 1) => flag `i8 (sgt `i8 x y);
      xor `i16 (flag `i16 (sle `i16 x y)) (i16 1) => flag `i16 (sgt `i16 x y);
      xor `i32 (flag `i32 (sle `i32 x y)) (i32 1l) => flag `i32 (sgt `i32 x y);
      xor `i64 (flag `i64 (sle `i64 x y)) (i64 1L) => flag `i64 (sgt `i64 x y);
      (* flag (x < y) ^ 1 => x >= y *)
      xor `i8 (flag `i8 (lt `i8 x y)) (i8 1) => flag `i8 (ge `i8 x y);
      xor `i16 (flag `i16 (lt `i16 x y)) (i16 1) => flag `i16 (ge `i16 x y);
      xor `i32 (flag `i32 (lt `i32 x y)) (i32 1l) => flag `i32 (ge `i32 x y);
      xor `i64 (flag `i64 (lt `i64 x y)) (i64 1L) => flag `i64 (ge `i64 x y);
      xor `i8 (flag `i8 (slt `i8 x y)) (i8 1) => flag `i8 (sge `i8 x y);
      xor `i16 (flag `i16 (slt `i16 x y)) (i16 1) => flag `i16 (sge `i16 x y);
      xor `i32 (flag `i32 (slt `i32 x y)) (i32 1l) => flag `i32 (sge `i32 x y);
      xor `i64 (flag `i64 (slt `i64 x y)) (i64 1L) => flag `i64 (sge `i64 x y);
      (* unsigned x < 0 = false *)
      lt `i8 x (i8 0) => bool false;
      lt `i16 x (i16 0) => bool false;
      lt `i32 x (i32 0l) => bool false;
      lt `i64 x (i64 0L) => bool false;
      (* unsigned x >= 0 = true *)
      ge `i8 x (i8 0) => bool true;
      ge `i16 x (i16 0) => bool true;
      ge `i32 x (i32 0l) => bool true;
      ge `i64 x (i64 0L) => bool true;
      (* unsigned x <= 0 = x == 0 *)
      le `i8 x (i8 0) => eq `i8 x (i8 0);
      le `i16 x (i16 0) => eq `i16 x (i16 0);
      le `i32 x (i32 0l) => eq `i32 x (i32 0l);
      le `i64 x (i64 0L) => eq `i64 x (i64 0L);
      (* unsigned x > 0 = x != 0 *)
      gt `i8 x (i8 0) => ne `i8 x (i8 0);
      gt `i16 x (i16 0) => ne `i16 x (i16 0);
      gt `i32 x (i32 0l) => ne `i32 x (i32 0l);
      gt `i64 x (i64 0L) => ne `i64 x (i64 0L);
      (* unsigned x < 0xff... = x != 0xff... *)
      lt `i8 x (i8 0xff) => ne `i8 x (i8 0xff);
      lt `i16 x (i16 0xffff) => ne `i16 x (i16 0xffff);
      lt `i32 x (i32 0xffff_ffffl) => ne `i32 x (i32 0xffff_ffffl);
      lt `i64 x (i64 0xffff_ffff_ffff_ffffL) => ne `i64 x (i64 0xffff_ffff_ffff_ffffL);
      (* unsigned x <= 0xff... = true *)
      le `i8 x (i8 0xff) => bool true;
      le `i16 x (i16 0xffff) => bool true;
      le `i32 x (i32 0xffff_ffffl) => bool true;
      le `i64 x (i64 0xffff_ffff_ffff_ffffL) => bool true;
      (* unsigned x > 0xff... = false *)
      gt `i8 x (i8 0xff) => bool false;
      gt `i16 x (i16 0xffff) => bool false;
      gt `i32 x (i32 0xffff_ffffl) => bool false;
      gt `i64 x (i64 0xffff_ffff_ffff_ffffL) => bool false;
      (* unsigned x >= 0xff... = x == 0xff... *)
      ge `i8 x (i8 0xff) => eq `i8 x (i8 0xff);
      ge `i16 x (i16 0xffff) => eq `i16 x (i16 0xffff);
      ge `i32 x (i32 0xffff_ffffl) => eq `i32 x (i32 0xffff_ffffl);
      ge `i64 x (i64 0xffff_ffff_ffff_ffffL) => eq `i64 x (i64 0xffff_ffff_ffff_ffffL);
      (* signed x < 0x80... = false *)
      slt `i8 x (i8 0x80) => bool false;
      slt `i16 x (i16 0x8000) => bool false;
      slt `i32 x (i32 0x8000_0000l) => bool false;
      slt `i64 x (i64 0x8000_0000_0000_0000L) => bool false;
      (* signed x <= 0x80... = x == 0x80... *)
      sle `i8 x (i8 0x80) => eq `i8 x (i8 0x80);
      sle `i16 x (i16 0x8000) => eq `i16 x (i16 0x8000);
      sle `i32 x (i32 0x8000_0000l) => eq `i32 x (i32 0x8000_0000l);
      sle `i64 x (i64 0x8000_0000_0000_0000L) => eq `i64 x (i64 0x8000_0000_0000_0000L);
      (* signed x > 0x80... = x != 0x80... *)
      sgt `i8 x (i8 0x80) => ne `i8 x (i8 0x80);
      sgt `i16 x (i16 0x8000) => ne `i16 x (i16 0x8000);
      sgt `i32 x (i32 0x8000_0000l) => ne `i32 x (i32 0x8000_0000l);
      sgt `i64 x (i64 0x8000_0000_0000_0000L) => ne `i64 x (i64 0x8000_0000_0000_0000L);
      (* signed x >= 0x80... = true *)
      sge `i8 x (i8 0x80) => bool true;
      sge `i16 x (i16 0x8000) => bool true;
      sge `i32 x (i32 0x8000_0000l) => bool true;
      sge `i64 x (i64 0x8000_0000_0000_0000L) => bool true;
      (* signed x > 0x7f... = false *)
      sgt `i8 x (i8 0x7f) => bool false;
      sgt `i16 x (i16 0x7fff) => bool false;
      sgt `i32 x (i32 0x7fff_ffffl) => bool false;
      sgt `i64 x (i64 0x7fff_ffff_ffff_ffffL) => bool false;
      (* signed x >= 0x7f... = x == 0x7f... *)
      sge `i8 x (i8 0x7f) => eq `i8 x (i8 0x7f);
      sge `i16 x (i16 0x7fff) => eq `i16 x (i16 0x7fff);
      sge `i32 x (i32 0x7fff_ffffl) => eq `i32 x (i32 0x7fff_ffffl);
      sge `i64 x (i64 0x7fff_ffff_ffff_ffffL) => eq `i64 x (i64 0x7fff_ffff_ffff_ffffL);
      (* signed x < 0x7f... = x != 0x7f... *)
      slt `i8 x (i8 0x7f) => ne `i8 x (i8 0x7f);
      slt `i16 x (i16 0x7fff) => ne `i16 x (i16 0x7fff);
      slt `i32 x (i32 0x7fff_ffffl) => ne `i32 x (i32 0x7fff_ffffl);
      slt `i64 x (i64 0x7fff_ffff_ffff_ffffL) => ne `i64 x (i64 0x7fff_ffff_ffff_ffffL);
      (* signed x <= 0x7f... = true *)
      sle `i8 x (i8 0x7f) => bool true;
      sle `i16 x (i16 0x7fff) => bool true;
      sle `i32 x (i32 0x7fff_ffffl) => bool true;
      sle `i64 x (i64 0x7fff_ffff_ffff_ffffL) => bool true;
      (* extend i8 x = x *)
      sext `i8 x => x;
      zext `i8 x => x;
      (* extend (extend x) = extend x *)
      sext `i16 (sext `i16 x) => sext `i16 x;
      sext `i32 (sext `i16 x) => sext `i32 x;
      sext `i32 (sext `i32 x) => sext `i32 x;
      sext `i64 (sext `i16 x) => sext `i64 x;
      sext `i64 (sext `i32 x) => sext `i64 x;
      sext `i64 (sext `i64 x) => sext `i64 x;
      zext `i16 (zext `i16 x) => zext `i16 x;
      zext `i32 (zext `i16 x) => zext `i32 x;
      zext `i32 (zext `i32 x) => zext `i32 x;
      zext `i64 (zext `i16 x) => zext `i64 x;
      zext `i64 (zext `i32 x) => zext `i64 x;
      zext `i64 (zext `i64 x) => zext `i64 x;
      (* br true, x, y = jmp x *)
      br (bool true) x y => jmp x;
      (* br false, x, y = jmp y *)
      br (bool false) x y => jmp y;
      (* br x, y, y = jmp y. *)
      br x y y => jmp y;
      (* true ? x : y = x. *)
      sel `i8 (bool true) x y => x;
      sel `i16 (bool true) x y => x;
      sel `i32 (bool true) x y => x;
      sel `i64 (bool true) x y => x;
      sel `f32 (bool true) x y => x;
      sel `f64 (bool true) x y => x;
      (* false ? x : y = y *)
      sel `i8 (bool false) x y => y;
      sel `i16 (bool false) x y => y;
      sel `i32 (bool false) x y => y;
      sel `i64 (bool false) x y => y;
      sel `f32 (bool false) x y => y;
      sel `f64 (bool false) x y => y;
      (* x ? y : y = y. *)
      sel `i8 x y y => y;
      sel `i16 x y y => y;
      sel `i32 x y y => y;
      sel `i64 x y y => y;
      sel `f32 x y y => y;
      sel `f64 x y y => y;
      (* Specialize to `flag`. *)
      sel `i8 x (i8 1) (i8 0) => flag `i8 x;
      sel `i16 x (i16 1) (i16 0) => flag `i16 x;
      sel `i32 x (i32 1l) (i32 0l) => flag `i32 x;
      sel `i64 x (i64 1L) (i64 0L) => flag `i64 x;
      sel `i8 x (i8 0)  (i8 1) => xor `i8 (flag `i8 x) (i8 1);
      sel `i16 x (i16 0) (i16 1) => xor `i16 (flag `i16 x) (i16 1);
      sel `i32 x (i32 0l) (i32 1l) => xor `i32 (flag `i32 x) (i32 1l);
      sel `i64 x (i64 0L) (i64 1L) => xor `i64 (flag `i64 x) (i64 1L);
      (* Copy propagation. *)
      copy `i8 x => x;
      copy `i16 x => x;
      copy `i32 x => x;
      copy `i64 x => x;
      copy `f32 x => x;
      copy `f64 x => x;
    ]
end

let cost ~child n =
  let init = match Egraph.Enode.op n with
    | Oaddr _
    | Obool _
    | Ocall0
    | Ocall _
    | Ocallargs
    | Odouble _
    | Oint _
    | Ojmp
    | Olocal _
    | Oret
    | Osingle _
    | Osym _
    | Oset _ -> 0
    | Obr | Otbl _ | Ovar _ -> 1
    | Osw _ | (Obinop #Insn.bitwise_binop) | Ounop _ -> 2
    | Obinop (`div _ | `udiv _ | `rem _ | `urem _) -> 25
    | Obinop _ | Oload _ | Ostore _ -> 3
    | Osel _ -> 6 in
  Egraph.Enode.children n |>
  List.fold ~init ~f:(fun k c -> k + child c)

let run fn =
  let*? eg = Egraph.create fn in
  let _ = Egraph.fixpoint eg Rules.rules in
  let ex = Egraph.Extractor.init eg ~cost in
  Egraph.Extractor.reify ex
