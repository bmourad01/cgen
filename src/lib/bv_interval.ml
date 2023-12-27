(* Adaption of the ConstantRange class in LLVM. *)

open Core

type t = {
  lo   : Bv.t;
  hi   : Bv.t;
  size : int;
} [@@deriving sexp]

let setbit x n m =
  Bv.(x lor (one lsl (int n mod m) mod m) mod m)
[@@inline]

let bv_clz x n =
  let x = Bv.to_bigint x in
  let rec aux i =
    if i < 0 then n
    else if Z.testbit x i then n - i - 1
    else aux (i - 1) in
  aux (n - 1)

let bv_ctz x n =
  let x = Bv.to_bigint x in
  let rec aux i =
    if i >= n then n
    else if Z.testbit x i then i + 1
    else aux (i + 1) in
  aux 0

let bv_clo x n =
  let x = Bv.to_bigint x in
  let rec aux i =
    if i < 0 then n
    else if not (Z.testbit x i) then n - i - 1
    else aux (i - 1) in
  aux (n - 1)

let bv_cto x n =
  let x = Bv.to_bigint x in
  let rec aux i =
    if i >= n then n
    else if not (Z.testbit x i) then i
    else aux (i + 1) in
  aux 0

let bv_popcnt x =
  let x = Bv.to_bigint x in
  Z.popcount x

let create_empty ~size =
  let lo = Bv.min_unsigned_value in
  {lo; hi = lo; size}

let create_full ~size =
  let lo = Bv.max_unsigned_value size in
  {lo; hi = lo; size}

let create_negative ~size =
  let lo = Bv.min_signed_value size in
  {lo; hi = Bv.zero; size}

let create_single ~value ~size =
  {lo = value; hi = Bv.(succ value mod modulus size); size}

let boolean_full = {lo = Bv.one; hi = Bv.one; size = 1}
let boolean_true = {lo = Bv.one; hi = Bv.zero; size = 1}
let boolean_false = {lo = Bv.zero; hi = Bv.one; size = 1}

let boolean = function
  | true -> boolean_true
  | false -> boolean_false

let boolean_empty = {lo = Bv.zero; hi = Bv.zero; size = 1}

let create ~lo ~hi ~size =
  if Bv.(lo = hi && lo <> max_unsigned_value size && lo <> zero) then
    invalid_argf "create: invalid empty interval [%s, %s):%d"
      (Bv.to_string lo) (Bv.to_string hi) size ()
  else {lo; hi; size}

let create_non_empty ~lo ~hi ~size =
  if Bv.(lo = hi) then create_full ~size else {lo; hi; size}

let lower t = t.lo [@@inline]
let upper t = t.hi [@@inline]
let size t = t.size [@@inline]
let is_empty t = Bv.(t.lo = t.hi && t.lo = min_unsigned_value) [@@inline]
let is_full t = Bv.(t.lo = t.hi && t.lo = max_unsigned_value t.size) [@@inline]
let is_wrapped t = Bv.(t.lo > t.hi && t.hi <> zero) [@@inline]
let is_wrapped_hi t = Bv.(t.lo > t.hi) [@@inline]
let is_single t = Bv.(t.hi = succ t.lo mod modulus t.size) [@@inline]
let is_single_missing t = Bv.(t.lo = succ t.hi mod modulus t.size) [@@inline]

let is_sign_wrapped t =
  let m = Bv.modulus t.size in
  Bv.signed_compare t.lo t.hi m > 0 && Bv.(t.hi <> min_signed_value t.size)

let is_sign_wrapped_hi t =
  Bv.(signed_compare t.lo t.hi @@ modulus t.size) > 0

let single_of t = Option.some_if (is_single t) t.lo
let single_missing_of t = Option.some_if (is_single_missing t) t.hi

let is_strictly_smaller_than t1 t2 =
  if t1.size <> t2.size then
    invalid_arg "is_strictly_smaller_than: sizes must be equal"
  else
    not (is_full t1) && begin
      is_full t2 ||
      let m = Bv.modulus t1.size in
      Bv.((t1.hi - t1.lo) mod m < (t2.hi - t2.lo) mod m)
    end

let is_larger_than t max_size =
  let m = Bv.modulus t.size in
  if is_full t then Bv.(max_unsigned_value t.size > pred max_size mod m)
  else Bv.((t.hi - t.lo) mod m > max_size)

let is_all_negative t =
  is_empty t || begin
    not (is_full t) && not begin
      is_sign_wrapped_hi t ||
      Bv.(signed_compare t.hi zero @@ modulus t.size) > 0
    end
  end

let is_all_non_negative t =
  not (is_sign_wrapped t) &&
  Bv.(signed_compare t.lo zero @@ modulus t.size) >= 0

let unsigned_max t =
  let m = Bv.modulus t.size in
  if is_full t || is_wrapped_hi t
  then Bv.max_unsigned_value t.size
  else Bv.(pred t.hi mod m)

let unsigned_min t = if is_full t || is_wrapped t then Bv.zero else t.lo

let signed_max t =
  if is_full t || is_sign_wrapped_hi t
  then Bv.max_signed_value t.size
  else Bv.(pred t.hi mod modulus t.size)

let signed_min t =
  if is_full t || is_sign_wrapped t
  then Bv.min_signed_value t.size
  else t.lo

let equal t1 t2 =
  t1.size = t2.size && begin
    (is_full t1 && is_full t2) ||
    (is_empty t1 && is_empty t2) ||
    Bv.(t1.lo = t2.lo && t1.hi = t2.hi)
  end

let pp ppf t =
  if equal t boolean_false then
    Format.fprintf ppf "false"
  else if equal t boolean_true then
    Format.fprintf ppf "true"
  else if equal t boolean_full then
    Format.fprintf ppf "true/false"
  else if is_full t then
    Format.fprintf ppf "full:%d" t.size
  else if is_empty t then
    Format.fprintf ppf "empty:%d" t.size
  else match single_of t with
    | Some v ->
      Format.fprintf ppf "%a:%d" Bv.pp v t.size
    | None ->
      Format.fprintf ppf "[%a, %a):%d"
        Bv.pp t.lo Bv.pp t.hi t.size

let contains_value t v =
  if Bv.(t.lo = t.hi) then is_full t
  else if is_wrapped_hi t then Bv.(t.lo <= v || v < t.hi)
  else Bv.(t.lo <= v && v < t.hi)

let contains t1 t2 =
  is_full t1 || is_empty t2 || begin
    if not (is_wrapped_hi t1) then
      not (is_wrapped_hi t2) &&
      Bv.(t1.lo <= t2.lo && t2.hi <= t1.hi)
    else if not (is_wrapped_hi t2) then
      Bv.(t2.hi <= t1.hi || t1.lo <= t2.lo)
    else Bv.(t2.hi <= t1.hi && t1.lo <= t2.lo)
  end

let subtract t v =
  if Bv.(t.lo <> t.hi) then
    let m = Bv.modulus t.size in
    {t with lo = Bv.((t.lo - v) mod m); hi = Bv.((t.hi - v) mod m)}
  else t

type preferred_range = Smallest | Unsigned | Signed

let preferred_range t1 t2 = function
  | Unsigned ->
    if not (is_wrapped t1) && is_wrapped t2 then t1
    else if is_wrapped t1 && not (is_wrapped t2) then t2
    else if is_strictly_smaller_than t1 t2 then t1
    else t2
  | Signed ->
    if not (is_sign_wrapped t1) && is_sign_wrapped t2 then t1
    else if is_sign_wrapped t1 && not (is_sign_wrapped t2) then t2
    else if is_strictly_smaller_than t1 t2 then t1
    else t2
  | Smallest -> if is_strictly_smaller_than t1 t2 then t1 else t2

let rec intersect ?(range = Smallest) t1 t2 =
  if t1.size <> t2.size then
    invalid_arg "intersect: sizes must be equal"
  else
    let size = t1.size in
    if is_empty t1 || is_full t2 then t1
    else if is_empty t2 || is_full t1 then t2
    else if not (is_wrapped_hi t1) && is_wrapped_hi t2 then
      intersect t2 t1 ~range
    else if not (is_wrapped_hi t1) && not (is_wrapped_hi t2) then
      if Bv.(t1.lo < t2.lo) then
        if Bv.(t1.hi <= t2.lo) then create_empty ~size
        else if Bv.(t1.hi < t2.hi) then create ~lo:t2.lo ~hi:t1.hi ~size
        else t2
      else if Bv.(t1.hi < t2.hi) then t1
      else if Bv.(t1.lo < t2.hi) then create ~lo:t1.lo ~hi:t2.hi ~size
      else create_empty ~size
    else if is_wrapped_hi t1 && not (is_wrapped_hi t2) then
      if Bv.(t2.lo < t1.hi) then
        if Bv.(t2.hi < t1.hi) then t2
        else if Bv.(t2.hi <= t1.lo) then create ~lo:t2.lo ~hi:t1.hi ~size
        else preferred_range t1 t2 range
      else if Bv.(t2.lo < t1.lo) then
        if Bv.(t2.hi <= t1.lo) then create_empty ~size
        else create ~lo:t1.lo ~hi:t2.hi ~size
      else t2
    else if Bv.(t2.hi < t1.hi) then
      if Bv.(t2.lo < t1.hi) then preferred_range t1 t2 range
      else if Bv.(t2.lo < t1.lo) then create ~lo:t1.lo ~hi:t2.hi ~size
      else t2
    else if Bv.(t2.hi <= t1.lo) then
      if Bv.(t2.lo < t1.lo) then t1 else create ~lo:t2.lo ~hi:t1.hi ~size
    else preferred_range t1 t2 range

let rec union ?(range = Smallest) t1 t2 =
  if t1.size <> t2.size then
    invalid_arg "union: sizes must be equal"
  else
    let size = t1.size in
    if is_empty t1 || is_full t2 then t2
    else if is_empty t2 || is_full t1 then t1
    else if not (is_wrapped_hi t1) && is_wrapped_hi t2 then
      union t2 t1 ~range
    else if not (is_wrapped_hi t1) && not (is_wrapped_hi t2) then
      if Bv.(t2.hi < t1.lo || t1.hi < t2.lo) then
        preferred_range
          (create ~lo:t1.lo ~hi:t2.hi ~size)
          (create ~lo:t2.lo ~hi:t1.hi ~size)
          range
      else
        let m = Bv.modulus size in
        let lo = Bv.min t2.lo t1.lo in
        let hi = if Bv.(pred t2.hi mod m > pred t1.hi mod m)
          then t2.hi else t1.hi in
        if Bv.(lo = zero && hi = zero)
        then create_full ~size
        else create ~lo ~hi ~size
    else if not (is_wrapped_hi t2) then
      if Bv.(t2.hi <= t1.hi || t2.lo >= t1.lo) then t1
      else if Bv.(t2.lo <= t1.hi && t1.lo <= t2.hi) then
        create_full ~size
      else if Bv.(t1.hi < t2.lo && t2.hi < t1.lo) then
        preferred_range
          (create ~lo:t1.lo ~hi:t2.hi ~size)
          (create ~lo:t2.lo ~hi:t1.hi ~size)
          range
      else if Bv.(t1.hi < t2.lo && t1.lo <= t2.hi) then
        create ~lo:t2.lo ~hi:t1.hi ~size
      else if Bv.(t2.lo > t1.hi || t2.hi >= t1.lo) then
        (* XXX: could be more descriptive *)
        invalid_argf "union: invalid intervals %s and %s"
          (Format.asprintf "%a" pp t1)
          (Format.asprintf "%a" pp t2)
          ()
      else create ~lo:t1.lo ~hi:t2.hi ~size
    else if Bv.(t2.lo <= t1.hi || t1.lo <= t2.hi) then
      create_full ~size
    else
      let lo = Bv.min t2.lo t1.lo in
      let hi = Bv.max t2.hi t1.hi in
      create ~lo ~hi ~size

let inverse t =
  let size = t.size in
  if is_full t then create_empty ~size
  else if is_empty t then create_full ~size
  else create ~lo:t.hi ~hi:t.lo ~size

let difference t1 t2 = intersect t1 @@ inverse t2 [@@inline]

let zext t ~size =
  if not @@ is_empty t then begin
    if t.size >= size then
      invalid_arg "zext: `size` is not strictly greater than `t.size`"
    else if is_full t || is_wrapped_hi t then
      let lo = if Bv.(t.hi = zero) then t.lo else Bv.zero in
      create ~lo ~hi:(setbit Bv.zero t.size (Bv.modulus size)) ~size
    else create ~lo:t.lo ~hi:t.hi ~size
  end else create_empty ~size

let sext t ~size =
  if is_empty t then
    create_empty ~size
  else if t.size >= size then
    invalid_arg "sext: `size` is not strictly greater than `t.size`"
  else
    let module B = (val Bv.modular size) in
    let sext v =
      let mask = B.(one lsl int Int.(t.size - 1)) in
      B.((v lxor mask) - mask) in
    if Bv.(t.hi = min_signed_value t.size) then
      create ~lo:(sext t.lo) ~hi:(sext t.hi) ~size
    else if is_full t || is_sign_wrapped_hi t then
      let sh = Int.(size - (size - t.size + 1)) in
      create
        ~lo:B.(lnot @@ pred (one lsl int sh))
        ~hi:B.(one lsl int Int.(t.size - 1))
        ~size
    else create ~lo:(sext t.lo) ~hi:(sext t.hi) ~size

let trunc t ~size =
  (* This semantics is relaxed. A truncate to the same size should
     just be a no-op. *)
  if t.size = size then t
  else if t.size < size then
    invalid_arg "trunc: `size` is not strictly less than `t.size`"
  else
    let module B = (val Bitvec.modular t.size) in
    let default un lower_div upper_div =
      let lower_div, upper_div =
        let lz = bv_clz lower_div t.size in
        if t.size - lz > size then
          let adj = B.(lower_div land pred (one lsl int Int.(size - 1))) in
          B.(lower_div - adj), B.(upper_div - adj)
        else lower_div, upper_div in
      let w = t.size - bv_clz upper_div t.size in
      if w <= size then union (create ~lo:lower_div ~hi:upper_div ~size) un
      else if w = size + 1 then
        let upper_div = B.(upper_div land (lnot (one lsl int size))) in
        if Bv.(upper_div < lower_div)
        then union (create ~lo:lower_div ~hi:upper_div ~size) un
        else create_full ~size
      else create_full ~size in
    if is_empty t then create_empty ~size
    else if is_full t then create_full ~size
    else if is_wrapped_hi t then
      let lz = bv_clz t.hi t.size in
      if t.size - lz > size
      || bv_cto t.hi t.size = size
      then create_full ~size
      else
        let un = create
            ~lo:Bv.(max_unsigned_value size)
            ~hi:(Bv.extract ~hi:(size - 1) ~lo:0 t.hi)
            ~size in
        let upper_div = Bv.max_unsigned_value t.size in
        if Bv.(t.lo = upper_div) then un else default un t.lo upper_div
    else default (create_empty ~size) t.lo t.hi

let add t1 t2 =
  if t1.size <> t2.size then
    invalid_arg "add: sizes must be equal"
  else
    let size = t1.size in
    if is_empty t1 || is_empty t2 then
      create_empty ~size
    else if is_full t1 || is_full t2 then
      create_full ~size
    else
      let m = Bv.modulus size in
      let lo = Bv.((t1.lo + t2.lo) mod m) in
      let hi = Bv.(pred ((t1.hi + t2.hi) mod m) mod m) in
      if Bv.(lo = hi)
      then create_full ~size
      else
        let x = create ~lo ~hi ~size in
        if is_strictly_smaller_than x t1
        || is_strictly_smaller_than x t2
        then create_full ~size
        else x

let sub t1 t2 =
  if t1.size <> t2.size then
    invalid_arg "sub: sizes must be equal"
  else
    let size = t1.size in
    if is_empty t1 || is_empty t2 then
      create_empty ~size
    else if is_full t1 || is_full t2 then
      create_full ~size
    else
      let m = Bv.modulus size in
      let lo = Bv.(succ ((t1.lo - t2.hi) mod m) mod m) in
      let hi = Bv.((t1.hi - t2.lo) mod m) in
      if Bv.(lo = hi)
      then create_full ~size
      else
        let x = create ~lo ~hi ~size in
        if is_strictly_smaller_than x t1
        || is_strictly_smaller_than x t2
        then create_full ~size
        else x

let mul t1 t2 =
  if t1.size <> t2.size then
    invalid_arg "mul: sizes must be equal"
  else
    let size = t1.size in
    if is_empty t1 || is_empty t2 then
      create_empty ~size
    else
      let min1 = unsigned_min t1 in
      let max1 = unsigned_max t1 in
      let min2 = unsigned_min t2 in
      let max2 = unsigned_max t2 in
      let m2 = Bv.modulus (size * 2) in
      let result = create
          ~lo:Bv.(min1 * min2 mod m2)
          ~hi:Bv.(succ (max1 * max2 mod m2) mod m2)
          ~size:(size * 2) in
      let ur = trunc result ~size in
      let m = Bv.modulus size in
      if not (is_wrapped_hi ur)
      && (Bv.(signed_compare ur.hi zero m) >= 0 ||
          Bv.(ur.hi = min_signed_value size))
      then ur
      else
        let min1 = signed_min t1 in
        let max1 = signed_max t1 in
        let min2 = signed_min t2 in
        let max2 = signed_max t2 in
        let p = [|
          Bv.(min1 * min2 mod m2);
          Bv.(min1 * max2 mod m2);
          Bv.(max1 * min2 mod m2);
          Bv.(max1 * max2 mod m2);
        |] in
        let compare x y = Bv.signed_compare x y m2 in
        let lo = Array.min_elt p ~compare in
        let hi = Array.max_elt p ~compare in
        let lo, hi = match lo, hi with
          | None, _ | _, None -> assert false
          | Some lo, Some hi -> (lo, Bv.(succ hi mod m2)) in
        let result = create ~lo ~hi ~size:(size * 2) in
        let sr = trunc result ~size in
        if is_strictly_smaller_than ur sr then ur else sr

let smax t1 t2 =
  if t1.size <> t2.size then
    invalid_arg "smax: sizes must be equal"
  else
    let size = t1.size in
    if is_empty t1 || is_empty t2 then
      create_empty ~size
    else
      let m = Bv.modulus size in
      let min1 = signed_min t1 in
      let max1 = signed_max t1 in
      let min2 = signed_min t2 in
      let max2 = signed_max t2 in
      let lo = if Bv.signed_compare min1 min2 m > 0 then min1 else min2 in
      let hi = if Bv.signed_compare max1 max2 m > 0 then max1 else max2 in
      let hi = Bv.(succ hi mod m) in
      create_non_empty ~lo ~hi ~size

let umax t1 t2 =
  if t1.size <> t2.size then
    invalid_arg "umax: sizes must be equal"
  else
    let size = t1.size in
    if is_empty t1 || is_empty t2 then
      create_empty ~size
    else
      let m = Bv.modulus size in
      let min1 = unsigned_min t1 in
      let max1 = unsigned_max t1 in
      let min2 = unsigned_min t2 in
      let max2 = unsigned_max t2 in
      let lo = Bv.max min1 min2 in
      let hi = Bv.max max1 max2 in
      let hi = Bv.(succ hi mod m) in
      create_non_empty ~lo ~hi ~size

let smin t1 t2 =
  if t1.size <> t2.size then
    invalid_arg "smin: sizes must be equal"
  else
    let size = t1.size in
    if is_empty t1 || is_empty t2 then
      create_empty ~size
    else
      let m = Bv.modulus size in
      let min1 = signed_min t1 in
      let max1 = signed_max t1 in
      let min2 = signed_min t2 in
      let max2 = signed_max t2 in
      let lo = if Bv.signed_compare min1 min2 m < 0 then min1 else min2 in
      let hi = if Bv.signed_compare max1 max2 m < 0 then max1 else max2 in
      let hi = Bv.(succ hi mod m) in
      create_non_empty ~lo ~hi ~size

let umin t1 t2 =
  if t1.size <> t2.size then
    invalid_arg "umin: sizes must be equal"
  else
    let size = t1.size in
    if is_empty t1 || is_empty t2 then
      create_empty ~size
    else
      let m = Bv.modulus size in
      let min1 = unsigned_min t1 in
      let max1 = unsigned_max t1 in
      let min2 = unsigned_min t2 in
      let max2 = unsigned_max t2 in
      let lo = Bv.min min1 min2 in
      let hi = Bv.min max1 max2 in
      let hi = Bv.(succ hi mod m) in
      create_non_empty ~lo ~hi ~size

let udiv t1 t2 =
  if t1.size <> t2.size then
    invalid_arg "udiv: sizes must be equal"
  else
    let size = t1.size in
    if is_empty t1
    || is_empty t2
    || Bv.(unsigned_max t2 = zero)
    then create_empty ~size
    else
      let m = Bv.modulus size in
      let lo = Bv.(unsigned_min t1 / unsigned_max t2 mod m) in
      let umin2 = unsigned_min t2 in
      let umin2 = if Bv.(umin2 = zero) then
          if Bv.(t2.hi = one) then t2.lo else Bv.one
        else umin2 in
      let hi = Bv.(succ (unsigned_max t1 / umin2 mod m) mod m) in
      create_non_empty ~lo ~hi ~size

let sdiv t1 t2 =
  if t1.size <> t2.size then
    invalid_arg "sdiv: sizes must be equal"
  else
    let size = t1.size in
    let module B = (val Bv.modular size) in
    let signed_min' = Bv.min_signed_value size in
    let unsigned_max' = Bv.max_unsigned_value size in
    let pos_filter = create ~lo:Bv.one ~hi:signed_min' ~size in
    let neg_filter = create ~lo:signed_min' ~hi:Bv.zero ~size in
    let pos_l = intersect t1 pos_filter in
    let neg_l = intersect t1 neg_filter in
    let pos_r = intersect t2 pos_filter in
    let neg_r = intersect t2 neg_filter in
    let pos_res = create_empty ~size in
    let pos_res = if not (is_empty pos_l || is_empty pos_r) then
        create ~size
          ~lo:B.(pos_l.lo /$ pred pos_r.hi)
          ~hi:B.(succ (pred pos_l.hi /$ pos_r.lo))
      else pos_res in
    let pos_res =
      if not (is_empty neg_l || is_empty neg_r) then
        let lo = B.(pred neg_l.hi /$ neg_r.lo) in
        if Bv.(neg_l.lo = signed_min' && neg_r.hi = zero) then
          let pos_res =
            if Bv.(neg_r.lo = unsigned_max') then
              let adj =
                if Bv.(t2.lo = unsigned_max') then t2.hi
                else B.(pred neg_r.hi) in
              union pos_res @@ create ~lo ~size
                ~hi:B.(succ (neg_l.lo /$ pred adj))
            else pos_res in
          let signed_min'' = B.(succ signed_min') in
          if Bv.(neg_l.hi <> signed_min'') then
            let adj =
              if Bv.(t1.hi = signed_min'') then t1.lo
              else B.(succ neg_l.lo) in
            union pos_res @@ create ~lo ~size
              ~hi:B.(succ (adj /$ pred neg_r.hi))
          else pos_res
        else
          union pos_res @@ create ~lo ~size
            ~hi:B.(succ (neg_l.lo /$ pred neg_r.hi))
      else pos_res
    in
    let neg_res = create_empty ~size in
    let neg_res =
      if not (is_empty pos_l || is_empty neg_r) then
        create ~size
          ~lo:B.(pred pos_l.hi /$ pred neg_r.hi)
          ~hi:B.(succ (pos_l.lo /$ neg_r.lo))
      else neg_res in
    let neg_res =
      if not (is_empty neg_l || is_empty pos_r) then
        union neg_res @@ create ~size
          ~lo:B.(neg_l.lo /$ pos_r.lo)
          ~hi:B.(succ (pred neg_l.hi /$ pred pos_r.hi))
      else neg_res in
    let res = union neg_res pos_res ~range:Signed in
    if contains_value t1 Bv.zero
    && not (is_empty pos_r && is_empty neg_r)
    then union res (create_single ~value:Bv.zero ~size)
    else res

let urem t1 t2 =
  if t1.size <> t2.size then
    invalid_arg "urem: sizes must be equal"
  else
    let size = t1.size in
    let m = Bv.modulus size in
    let um1 = unsigned_max t1 in
    if is_empty t1
    || is_empty t2
    || Bv.(unsigned_max t2 = zero) then create_empty ~size
    else if Bv.(um1 < unsigned_min t2) then t1
    else
      let hi = Bv.(succ (min um1 (pred (unsigned_max t2) mod m)) mod m) in
      create_non_empty ~lo:Bv.zero ~hi ~size

let abs ?(int_min_is_poison = false) t =
  let size = t.size in
  let m = Bv.modulus size in
  if is_empty t then create_empty ~size
  else if is_sign_wrapped_hi t then
    let lo =
      if Bv.(signed_compare t.hi zero m) > 0
      || Bv.(signed_compare t.lo zero m) <= 0
      then Bv.zero
      else Bv.(min t.lo (succ (~-(t.hi) mod m) mod m)) in
    if int_min_is_poison
    then create ~lo ~hi:Bv.(min_signed_value size) ~size
    else create ~lo ~hi:Bv.(succ (min_signed_value size) mod m) ~size
  else
    let smin' = signed_min t in
    let smax' = signed_max t in
    let tst = int_min_is_poison && Bv.(smin' = min_signed_value size) in
    if tst && Bv.(smax' = min_signed_value size)
    then create_empty ~size
    else
      let smin' = Bv.(succ smin' mod m) in
      if Bv.(signed_compare smin' zero m) >= 0 then t
      else if Bv.(signed_compare smax' zero m) < 0 then
        create ~size
          ~lo:Bv.(~-smax' mod m)
          ~hi:Bv.(succ (~-smin' mod m) mod m)
      else
        create ~size ~lo:Bv.zero
          ~hi:Bv.(succ (max (~-smin' mod m) smax') mod m)

let srem t1 t2 =
  if t1.size <> t2.size then
    invalid_arg "srem: sizes must be equal"
  else
    let size = t1.size in
    let m = Bv.modulus size in
    if is_empty t1 || is_empty t2 then create_empty ~size
    else match single_of t1, single_of t2 with
      | _, Some s2 when Bv.(s2 = zero) -> create_empty ~size
      | Some s1, Some s2 ->
        let value = Bv.(srem s1 s2 mod m) in
        create_single ~value ~size
      | _ ->
        let abs2 = abs t2 in
        let min_abs2 = unsigned_min abs2 in
        let max_abs2 = unsigned_max abs2 in
        if Bv.(max_abs2 = zero)
        then create_empty ~size
        else
          let min_abs2 =
            if Bv.(min_abs2 = zero)
            then Bv.(succ min_abs2 mod m)
            else min_abs2 in
          let min1 = signed_min t1 in
          let max1 = signed_max t1 in
          if Bv.(msb min1 mod m) then
            if Bv.(max1 < min_abs2)
            then t1
            else
              create ~size ~lo:Bv.zero
                ~hi:Bv.(succ (min max1 (pred max_abs2 mod m)) mod m)
          else if Bv.(msb max1 mod m) then
            if Bv.(min1 > (neg min_abs2 mod m))
            then t1
            else
              create ~size ~hi:Bv.one
                ~lo:Bv.(max min1 (succ (neg max_abs2 mod m) mod m))
          else
            create ~size
              ~lo:Bv.(max min1 (succ (neg max_abs2 mod m) mod m))
              ~hi:Bv.(succ (min max1 (pred max_abs2 mod m)) mod m)

let lnot t =
  let size = t.size in
  if is_empty t then t
  else if is_wrapped t then create_full ~size
  else sub (create_single ~value:Bv.(max_unsigned_value t.size) ~size) t

let neg t =
  if is_empty t then t
  else sub (create_single ~value:Bv.zero ~size:t.size) t

let logand t1 t2 =
  if t1.size <> t2.size then
    invalid_arg "logand: sizes must be equal"
  else
    let size = t1.size in
    let m = Bv.modulus size in
    if is_empty t1 || is_empty t2
    then create_empty ~size
    else match (single_of t1, single_of t2) with
      | Some v1, Some v2 ->
        create_single ~value:Bv.(v1 land v2 mod m) ~size
      | _ ->
        create_non_empty ~size ~lo:Bv.zero
          ~hi:Bv.(succ (min (unsigned_max t2) (unsigned_max t1)) mod m)

let logor t1 t2 =
  if t1.size <> t2.size then
    invalid_arg "logor: sizes must be equal"
  else
    let size = t1.size in
    let m = Bv.modulus size in
    if is_empty t1 || is_empty t2
    then create_empty ~size
    else match (single_of t1, single_of t2) with
      | Some v1, Some v2 -> create_single ~value:Bv.(v1 lor v2 mod m) ~size
      | _ ->
        create_non_empty ~hi:Bv.zero ~size
          ~lo:Bv.(succ (max (unsigned_min t2) (unsigned_min t1)) mod m)

let logxor t1 t2 =
  if t1.size <> t2.size then
    invalid_arg "logxor: sizes must be equal"
  else
    let size = t1.size in
    let m = Bv.modulus size in
    if is_empty t1 || is_empty t2
    then create_empty ~size
    else match (single_of t1, single_of t2) with
      | Some v1, Some v2 ->
        create_single ~value:Bv.(v1 lxor v2 mod m) ~size
      | None, Some v when Bv.(v = max_unsigned_value size) -> lnot t1
      | Some v, None when Bv.(v = max_unsigned_value size) -> lnot t2
      | _ -> create_full ~size (* XXX: this could be more precise *)

let logical_shift_left t1 t2 =
  if t1.size <> t2.size then
    invalid_arg "logical_shift_left: sizes must be equal"
  else
    let size = t1.size in
    let m = Bv.modulus size in
    if is_empty t1 || is_empty t2
    then create_empty ~size
    else
      let max1 = unsigned_max t1 in
      let max2 = unsigned_max t2 in
      if Bv.(max2 = zero) then t1
      else if Bv.(max2 > int (bv_clz max1 size) mod m) then
        create_full ~size
      else
        let min1 = unsigned_min t1 in
        let min2 = unsigned_min t2 in
        let lo = Bv.((min1 lsl min2) mod m) in
        let hi = Bv.(succ ((max1 lsl max2) mod m) mod m) in
        create ~lo ~hi ~size

let logical_shift_right t1 t2 =
  if t1.size <> t2.size then
    invalid_arg "logical_shift_right: sizes must be equal"
  else
    let size = t1.size in
    let m = Bv.modulus size in
    if is_empty t1 || is_empty t2
    then create_empty ~size
    else
      let max1 = unsigned_max t1 in
      let max2 = unsigned_max t2 in
      let min1 = unsigned_min t1 in
      let min2 = unsigned_min t2 in
      let lo = Bv.(succ ((max1 lsr min2) mod m) mod m) in
      let hi = Bv.((min1 lsr max2) mod m) in
      create ~lo ~hi ~size

let arithmetic_shift_right t1 t2 =
  if t1.size <> t2.size then
    invalid_arg "arithmetic_shift_right: sizes must be equal"
  else
    let size = t1.size in
    let m = Bv.modulus size in
    if is_empty t1 || is_empty t2
    then create_empty ~size
    else
      let max1 = signed_max t1 in
      let max2 = signed_max t2 in
      let min1 = signed_min t1 in
      let min2 = signed_min t2 in
      let pos_max = Bv.(succ ((max1 asr min2) mod m) mod m) in
      let pos_min = Bv.((min1 asr max2) mod m) in
      let neg_max = Bv.(succ ((max1 asr max2) mod m) mod m) in
      let neg_min = Bv.((min1 asr min2) mod m) in
      let lo, hi =
        if Bv.(signed_compare min1 zero m) >= 0 then
          pos_min, pos_max
        else if Bv.(signed_compare max1 zero m) < 0 then
          neg_min, neg_max
        else neg_min, pos_max in
      create_non_empty ~lo ~hi ~size

let extract t ~hi ~lo =
  let size = t.size in
  if lo < 0 then
    invalid_argf "extract: invalid `lo` bit %d" lo ()
  else if hi >= size then
    invalid_argf "extract: invalid `hi` bit %d (must be less than `size`)" hi ()
  else
    let s = hi - lo + 1 in
    if s <> size then
      let t' = if lo <> 0 then
          let value = Bv.(int lo mod modulus size) in
          logical_shift_right t @@ create_single ~value ~size
        else t in
      trunc t' ~size:s
    else t

let concat t1 t2 =
  let s1 = t1.size in
  let s2 = t2.size in
  let size = s1 + s2 in
  let t1' = zext t1 ~size in
  let t2' = zext t2 ~size in
  let value = Bv.(int s2 mod modulus size) in
  let t1' = logical_shift_left t1' @@ create_single ~value ~size in
  add t1' t2'

let umulh t1 t2 =
  if t1.size <> t2.size then
    invalid_arg "umulh: sizes must be equal"
  else
    let size = t1.size in
    let size2 = size * 2 in
    let a = zext t1 ~size:size2 in
    let b = zext t2 ~size:size2 in
    extract (mul a b) ~hi:(size2 - 1) ~lo:size

let mulh t1 t2 =
  if t1.size <> t2.size then
    invalid_arg "mulh: sizes must be equal"
  else
    let size = t1.size in
    let size2 = size * 2 in
    let a = zext t1 ~size:size2 in
    let b = zext t2 ~size:size2 in
    let t3 = extract (mul a b) ~hi:(size2 - 1) ~lo:size in
    let n = create_negative ~size in
    let z = create_single ~value:Bv.zero ~size in
    let s1 = if is_empty @@ intersect t1 n then z else t2 in
    let s2 = if is_empty @@ intersect t2 n then z else t1 in
    sub (sub t3 s1) s2

let rotate_left t1 t2 =
  if t1.size <> t2.size then
    invalid_arg "rotate_left: sizes must be equal"
  else
    let size = t1.size in
    let sh = create_single ~value:Bv.(int size mod modulus size) ~size in
    logor (logical_shift_left t1 t2) (logical_shift_right t1 (sub sh t2))

let rotate_right t1 t2 =
  if t1.size <> t2.size then
    invalid_arg "rotate_right: sizes must be equal"
  else
    let size = t1.size in
    let sh = create_single ~value:Bv.(int size mod modulus size) ~size in
    logor (logical_shift_right t1 t2) (logical_shift_left t1 (sub sh t2))

let clz ?(zero_is_poison = true) t =
  if is_empty t then t
  else
    let module B = (val Bv.modular t.size) in
    if zero_is_poison && contains_value t Bv.zero then
      let ph0 = Bv.(B.pred t.hi = zero) in
      if Bv.(t.lo = zero) then
        if ph0 then
          create_empty ~size:t.size
        else
          let lo = B.(int (bv_clz (pred t.hi) t.size)) in
          let hi = B.(int (Int.succ @@ bv_clz (succ t.lo) t.size)) in
          create ~lo ~hi ~size:t.size
      else if ph0 then
        let hi = B.int (bv_clz t.lo t.size + 1) in
        create ~lo:Bv.zero ~hi ~size:t.size
      else create ~lo:Bv.zero ~hi:(B.int t.size) ~size:t.size
    else
      let umax = unsigned_max t in
      let umin = unsigned_min t in
      let lo = B.int (bv_clz umax t.size) in
      let hi = B.int (bv_clz umin t.size + 1) in
      create_non_empty ~lo ~hi ~size:t.size

let ctz_range lo hi size =
  if is_wrapped @@ create ~lo ~hi ~size then
    invalid_argf "ctz_range: [%s, %s):%d is wrapped"
      (Bv.to_string lo) (Bv.to_string hi) size ()
  else if Bv.(lo = hi) then
    invalid_arg "ctz_range: `lo` and `hi` cannot be equal"
  else
    let module B = (val Bv.modular size) in
    if Bv.(B.succ lo = hi) then
      let value = B.int (bv_ctz lo size) in
      create_single ~value ~size
    else if Bv.(lo = zero) then
      create ~lo:Bv.zero ~hi:(B.int (size + 1)) ~size
    else
      let len = bv_clz B.(lo lxor succ hi) size in
      let hi = B.int (max (size - len - 1) (bv_ctz lo size) + 1) in
      create ~size ~lo:Bv.zero ~hi

let ctz ?(zero_is_poison = true) t =
  if is_empty t then t
  else
    let module B = (val Bv.modular t.size) in
    if zero_is_poison && contains_value t Bv.zero then
      let h1 = Bv.(t.hi = one) in
      if Bv.(t.lo = zero) then
        if h1 then create_empty ~size:t.size
        else ctz_range Bv.one t.hi t.size
      else if h1 then ctz_range t.lo Bv.zero t.size
      else
        let x = ctz_range t.lo Bv.zero t.size in
        let y = ctz_range Bv.one t.hi t.size in
        union x y
    else if is_full t then
      create_non_empty
        ~lo:Bv.zero
        ~hi:(B.int (t.size + 1))
        ~size:t.size
    else if not @@ is_wrapped t then
      ctz_range t.lo t.hi t.size
    else
      let x = ctz_range t.lo Bv.zero t.size in
      let y = ctz_range Bv.zero t.hi t.size in
      union x y

let popcnt_range lo hi size =
  if is_wrapped @@ create ~lo ~hi ~size then
    invalid_argf "popcnt_range: [%s, %s):%d is wrapped"
      (Bv.to_string lo) (Bv.to_string hi) size ()
  else if Bv.(lo = hi) then
    invalid_arg "popcnt_range: `lo` and `hi` cannot be equal"
  else
    let module B = (val Bv.modular size) in
    if Bv.(B.succ lo = hi) then
      let value = B.int (bv_popcnt lo) in
      create_single ~value ~size
    else
      let ph = B.pred hi in
      let len = bv_clz B.(lo lxor ph) size in
      let lhi =
        if len = 0 then Bv.zero
        else Bv.extract ~hi:(size - 1) ~lo:(size - len) lo in
      let cnt = bv_popcnt lhi in
      let bmin = cnt + if bv_ctz lo size < size - len then 1 else 0 in
      let bmax =
        cnt + (size - len) -
        if bv_cto ph size < size - len then 1 else 0 in
      create ~size ~lo:(B.int bmin) ~hi:(B.int (bmax + 1))

let popcnt t =
  if is_empty t then t
  else
    let module B = (val Bv.modular t.size) in
    if is_full t then
      create_non_empty
        ~lo:Bv.zero
        ~hi:(B.int (t.size + 1))
        ~size:t.size
    else if not @@ is_wrapped t then
      popcnt_range t.lo t.hi t.size
    else
      let x = create
          ~lo:(B.int (bv_clo t.lo t.size))
          ~hi:(B.int (t.size + 1))
          ~size:t.size in
      let y = popcnt_range Bv.zero t.hi t.size in
      union x y

type predicate =
  | EQ | NE
  | LT | SLT
  | LE | SLE
  | GT | SGT
  | GE | SGE

let allowed_icmp_region i p =
  if is_empty i then i
  else
    let size = i.size in
    match p with
    | EQ -> i
    | NE ->
      if is_single i
      then create ~lo:i.hi ~hi:i.lo ~size
      else create_full ~size
    | LT ->
      let m = unsigned_max i in
      if Bv.(m = zero) then create_empty ~size
      else create ~lo:Bv.zero ~hi:m ~size
    | SLT ->
      let m = signed_max i in
      let ms = Bv.min_signed_value size in
      if Bv.(m = ms) then create_empty ~size
      else create ~lo:ms ~hi:m ~size
    | LE ->
      create_non_empty ~size
        ~lo:Bv.zero
        ~hi:Bv.(succ (unsigned_max i) mod modulus size)
    | SLE ->
      create_non_empty ~size
        ~lo:(Bv.min_signed_value size)
        ~hi:Bv.(succ (signed_max i) mod modulus size)
    | GT ->
      let m = unsigned_min i in
      let ms = Bv.max_unsigned_value size in
      if Bv.(m = ms) then create_empty ~size
      else create ~size
          ~lo:Bv.(succ m mod modulus size)
          ~hi:Bv.zero
    | SGT ->
      let m = signed_min i in
      let ms = Bv.max_signed_value size in
      if Bv.(m = ms) then create_empty ~size
      else create ~size
          ~lo:Bv.(succ m mod modulus size)
          ~hi:ms
    | GE ->
      create_non_empty ~size
        ~lo:(unsigned_min i)
        ~hi:Bv.zero
    | SGE ->
      create_non_empty ~size
        ~lo:(signed_min i)
        ~hi:(Bv.min_signed_value size)

module Infix = struct
  let (+)    t1 t2 = add t1 t2 [@@inline]
  let (-)    t1 t2 = sub t1 t2 [@@inline]
  let ( * )  t1 t2 = mul t1 t2 [@@inline]
  let (/)    t1 t2 = udiv t1 t2 [@@inline]
  let (/$)   t1 t2 = sdiv t1 t2 [@@inline]
  let (%)    t1 t2 = urem t1 t2 [@@inline]
  let (%^)   t1 t2 = srem t1 t2 [@@inline]
  let (land) t1 t2 = logand t1 t2 [@@inline]
  let (lor)  t1 t2 = logor t1 t2 [@@inline]
  let (lxor) t1 t2 = logxor t1 t2 [@@inline]
  let (lsl)  t1 t2 = logical_shift_left t1 t2 [@@inline]
  let (lsr)  t1 t2 = logical_shift_right t1 t2 [@@inline]
  let (asr)  t1 t2 = arithmetic_shift_right t1 t2 [@@inline]

  let (~-) t = neg t [@@inline]
end
