(* Infer the interval constraints from a comparison op. *)

open Core
open Virtual
open Sccp_intervals_common

(* Constrain `y` to `i` in relation to the condition `x`. *)
let add_constraint ctx x y i = match (y : operand) with
  | `var y ->
    let i = Lazy.force i in
    Hashtbl.update ctx.cond x ~f:(function
        | None -> Var.Map.singleton y i
        | Some s -> update s y i)
  | _ -> ()

type predicate =
  | EQ | NE
  | LT | SLT
  | LE | SLE
  | GT | SGT
  | GE | SGE

let allowed_icmp_region size i p =
  if I.is_empty i then i
  else match p with
    | EQ -> i
    | NE ->
      if I.is_single i
      then I.create ~lo:(I.upper i) ~hi:(I.lower i) ~size
      else I.create_full ~size
    | LT ->
      let m = I.unsigned_max i in
      if Bv.(m = zero) then I.create_empty ~size
      else I.create ~lo:Bv.zero ~hi:m ~size
    | SLT ->
      let m = I.signed_max i in
      let ms = Bv.min_signed_value size in
      if Bv.(m = ms) then I.create_empty ~size
      else I.create ~lo:ms ~hi:m ~size
    | LE ->
      I.create_non_empty ~size
        ~lo:Bv.zero
        ~hi:Bv.(succ (I.unsigned_max i) mod modulus size)
    | SLE ->
      I.create_non_empty ~size
        ~lo:(Bv.min_signed_value size)
        ~hi:Bv.(succ (I.signed_max i) mod modulus size)
    | GT ->
      let m = I.unsigned_min i in
      let ms = Bv.max_unsigned_value size in
      if Bv.(m = ms) then I.create_empty ~size
      else I.create ~size
          ~lo:Bv.(succ m mod modulus size)
          ~hi:Bv.zero
    | SGT ->
      let m = I.signed_min i in
      let ms = Bv.max_signed_value size in
      if Bv.(m = ms) then I.create_empty ~size
      else I.create ~size
          ~lo:Bv.(succ m mod modulus size)
          ~hi:ms
    | GE ->
      I.create_non_empty ~size
        ~lo:(I.unsigned_min i)
        ~hi:Bv.zero
    | SGE ->
      I.create_non_empty ~size
        ~lo:(I.signed_min i)
        ~hi:(Bv.min_signed_value size)

let eq size a b =
  lazy (I.inverse @@ allowed_icmp_region size b NE),
  lazy (I.inverse @@ allowed_icmp_region size a NE)

let ne size a b =
  lazy (I.inverse @@ allowed_icmp_region size b EQ),
  lazy (I.inverse @@ allowed_icmp_region size a EQ)

let lt size a b =
  lazy (I.inverse @@ allowed_icmp_region size b GE),
  lazy (I.inverse @@ allowed_icmp_region size a LE)

let le size a b =
  lazy (I.inverse @@ allowed_icmp_region size b GT),
  lazy (I.inverse @@ allowed_icmp_region size a LT)

let gt size a b =
  lazy (I.inverse @@ allowed_icmp_region size b LE),
  lazy (I.inverse @@ allowed_icmp_region size a GE)

let ge size a b =
  lazy (I.inverse @@ allowed_icmp_region size b LT),
  lazy (I.inverse @@ allowed_icmp_region size a GT)

let slt size a b =
  lazy (I.inverse @@ allowed_icmp_region size b SGE),
  lazy (I.inverse @@ allowed_icmp_region size a SLE)

let sle size a b =
  lazy (I.inverse @@ allowed_icmp_region size b SGT),
  lazy (I.inverse @@ allowed_icmp_region size a SLT)

let sgt size a b =
  lazy (I.inverse @@ allowed_icmp_region size b SLE),
  lazy (I.inverse @@ allowed_icmp_region size a SGE)

let sge size a b =
  lazy (I.inverse @@ allowed_icmp_region size b SLT),
  lazy (I.inverse @@ allowed_icmp_region size a SGT)
