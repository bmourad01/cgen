(* This is the "magic division by constants" algorithm from
   Hacker's Delight, and adapted to work with arbitrary-precision
   bitvectors. *)

open Core

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
      if p >= sz2 || (
          Bv.(q1 >= delta) &&
          Bv.(q1 <> delta || r1 <> B.zero)
        ) then loop a p q1 r1 q2 r2
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
