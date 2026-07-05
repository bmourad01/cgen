(* This is the "magic division by constants" algorithm from
   Hacker's Delight, and adapted to work with arbitrary-precision
   bitvectors. *)

open Core

module Bv = Cgen_utils.Bv

let unsigned d t =
  if Bv.(d = zero || d = one) then
    invalid_argf "Cannot compute magic unsigned division of %s"
      (Bv.to_string d) ()
  else
    let sz = Type.sizeof_imm t in
    let sz1 = sz - 1 in
    let sz2 = sz * 2 in
    let module B = (val Bv.modular sz) in
    let nc = B.(ones - (~-d) % d) in
    let mins = B.(one lsl int sz1) in
    let maxs = B.(mins - one) in
    let rec loop a p q1 r1 q2 r2 =
      let p = p + 1 in
      let q1, r1 = if Bv.(B.(r1 >= (nc - r1)))
        then B.(q1 * int 2 + one, r1 * int 2 - nc)
        else B.(q1 * int 2, r1 * int 2) in
      let a, q2, r2 =
        if Bv.(B.(r2 + one >= d - r2)) then
          a || Bv.(q2 >= maxs),
          B.(q2 * int 2 + one),
          B.(((r2 * int 2) + one) - d)
        else
          a || Bv.(q2 >= mins),
          B.(q2 * int 2),
          B.(r2 * int 2 + one) in
      let delta = B.(d - one - r2) in
      (* Continue while we haven't converged, bounded by `sz2` iterations
         (the magic is guaranteed within `2 * sz`). The `sz2` bound must
         terminate the loop, not extend it: some divisors (e.g. 641) never
         hit the convergence exit, so without the bound `q1` runs away and
         the loop spins forever. *)
      if p < sz2 && Bv.(q1 < delta || (q1 = delta && r1 = B.zero))
      then loop a p q1 r1 q2 r2
      else B.(q2 + one), a, p - sz in
    let q1 = B.(mins / nc) in
    let r1 = B.(mins - q1 * nc) in
    let q2 = B.(maxs / d) in
    let r2 = B.(maxs - q2 * d) in
    loop false sz1 q1 r1 q2 r2

let signed d t =
  let sz = Type.sizeof_imm t in
  let module B = (val Bv.modular sz) in
  if Bv.(d = zero || d = one || d = B.(pred zero)) then
    invalid_argf "Cannot compute magic signed division of %s"
      (Bv.to_string d) ()
  else
    let sz1 = sz - 1 in
    let mins = B.(one lsl int sz1) in
    let ad = B.abs d in
    let t = B.(mins + bool (msb d)) in
    let anc = B.((t - one) - (t % ad)) in
    let rec loop p q1 r1 q2 r2 =
      let p = p + 1 in
      let q1 = B.(q1 * int 2) in
      let r1 = B.(r1 * int 2) in
      let q1, r1 = if Bv.(r1 >= anc)
        then B.(q1 + one, r1 - anc)
        else q1, r1 in
      let q2 = B.(q2 * int 2) in
      let r2 = B.(r2 * int 2) in
      let q2, r2 = if Bv.(r2 >= ad)
        then B.(q2 + one, r2 - ad)
        else q2, r2 in
      let delta = B.(ad - r2) in
      if Bv.(q1 < delta || (q1 = delta && r1 = zero))
      then loop p q1 r1 q2 r2
      else
        let m = B.(q2 + one) in
        (if B.msb d then B.neg m else m), p - sz in
    let q1 = B.(mins / anc) in
    let r1 = B.(mins - q1 * anc) in
    let q2 = B.(mins / ad) in
    let r2 = B.(mins - q2 * ad) in
    loop sz1 q1 r1 q2 r2

let mulinv a t =
  let sz = Type.sizeof_imm t in
  let module B = (val Bv.modular sz) in
  (* `a` is its own inverse modulo 8, and each Newton step
     `x <- x * (2 - a * x)` doubles the number of correct
     low bits. *)
  let two = B.int 2 in
  let rec loop x bits =
    if bits >= sz then x
    else loop B.(x * (two - a * x)) (bits * 2) in
  loop a 3

type divisible =
  | Pow2_mask of Bv.t
  | Test of {
      factor : Bv.t;
      bias   : Bv.t;
      rot    : int;
      limit  : Bv.t;
    }

let divisible ~signed d t =
  let sz = Type.sizeof_imm t in
  let module B = (val Bv.modular sz) in
  let ad = if signed then B.abs d else d in
  let mask = B.pred ad in
  if Bv.(B.(ad land mask) = zero) then Pow2_mask mask
  else
    (* `d = 2^k * q` with `q` odd. The low `k` bits are handled by the
       rotation, and `q` by the modular inverse. *)
    let k = Int64.ctz @@ Bv.to_int64 ad in
    let q = B.(ad lsr int k) in
    let factor = mulinv q t in
    if not signed then
      (* `x` divisible by `d` iff `ror (x * factor) k <= (2^W - 1) / d`. *)
      Test {factor; bias = B.zero; rot = k; limit = B.(ones / ad)}
    else
      (* Map the divisible values, which straddle zero, into a single
         unsigned range by adding `bias = (2^(W-1) / d) << k` before the
         rotation. *)
      let mins = B.(one lsl int Int.(sz - 1)) in
      let b0 = B.(mins / ad) in
      Test {
        factor;
        bias = B.(b0 lsl int k);
        rot = k;
        limit = B.(pred mins / ad + b0);
      }
