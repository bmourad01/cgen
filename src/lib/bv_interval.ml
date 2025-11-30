(* Adaption of the ConstantRange class in LLVM. *)

open Core

type t = {
  lo   : Bv.t;
  hi   : Bv.t;
  size : int;
} [@@deriving sexp]

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
      (Bv.to_string lo) (Bv.to_string hi) size ();
  {lo; hi; size}

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
  Bv.signed_compare t.lo t.hi t.size > 0 &&
  Bv.(t.hi <> min_signed_value t.size)

let is_sign_wrapped_hi t =
  Bv.(signed_compare t.lo t.hi t.size) > 0

let single_of t = Option.some_if (is_single t) t.lo
let single_missing_of t = Option.some_if (is_single_missing t) t.hi

let is_size_strictly_smaller_than t1 t2 =
  if t1.size <> t2.size then
    invalid_arg "is_size_strictly_smaller_than: sizes must be equal";
  if is_full t1 then false
  else if is_full t2 then true
  else
    let m = Bv.modulus t1.size in
    let s1 = Bv.((t1.hi - t1.lo) mod m) in
    let s2 = Bv.((t2.hi - t2.lo) mod m) in
    Bv.(s1 < s2)

let is_size_larger_than t max_size =
  let m = Bv.modulus t.size in
  if is_full t then
    Bv.(max_size = zero) ||
    Bv.(max_unsigned_value t.size > pred max_size mod m)
  else Bv.((t.hi - t.lo) mod m > max_size)

let is_all_negative t =
  is_empty t || begin
    not (is_full t) && not begin
      is_sign_wrapped_hi t ||
      Bv.(signed_compare t.hi zero t.size) > 0
    end
  end

let is_all_non_negative t =
  not (is_sign_wrapped t) &&
  Bv.(signed_compare t.lo zero t.size) >= 0

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

let to_string t = Format.asprintf "%a" pp t

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
    else if is_size_strictly_smaller_than t1 t2 then t1
    else t2
  | Signed ->
    if not (is_sign_wrapped t1) && is_sign_wrapped t2 then t1
    else if is_sign_wrapped t1 && not (is_sign_wrapped t2) then t2
    else if is_size_strictly_smaller_than t1 t2 then t1
    else t2
  | Smallest -> if is_size_strictly_smaller_than t1 t2 then t1 else t2

let rec intersect ?(range = Smallest) t1 t2 =
  if t1.size <> t2.size then
    invalid_arg "intersect: sizes must be equal";
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
    invalid_arg "union: sizes must be equal";
  let size = t1.size in
  let module B = (val Bv.modular size) in
  if      is_full t1 || is_empty t2 then t1
  else if is_full t2 || is_empty t1 then t2
  else if not (is_wrapped_hi t1) && is_wrapped_hi t2 then
    union t2 t1 ~range
  else if not (is_wrapped_hi t1) && not (is_wrapped_hi t2) then
    if Bv.(t2.hi < t1.lo || t1.hi < t2.lo) then
      let t1' = create ~lo:t1.lo ~hi:t2.hi ~size in
      let t2' = create ~lo:t2.lo ~hi:t1.hi ~size in
      preferred_range t1' t2' range
    else
      let l = if Bv.(t2.lo < t1.lo) then t2.lo else t1.lo in
      let u = if Bv.(B.pred t2.hi > B.pred t1.hi) then t2.hi else t1.hi in
      if Bv.(l = zero && u = zero) then
        create_full ~size
      else
        create ~lo:l ~hi:u ~size
  else if not (is_wrapped_hi t2) then
    if Bv.(t2.hi <= t1.hi || t2.lo >= t1.lo) then t1
    else if Bv.(t2.lo <= t1.hi && t1.lo <= t2.hi) then
      create_full ~size
    else if Bv.(t1.hi < t2.lo && t2.hi < t1.lo) then
      let t1' = create ~lo:t1.lo ~hi:t2.hi ~size in
      let t2' = create ~lo:t2.lo ~hi:t1.hi ~size in
      preferred_range t1' t2' range
    else if Bv.(t1.hi < t2.lo && t1.lo <= t2.hi) then
      create ~lo:t2.lo ~hi:t1.hi ~size
    else if Bv.(t2.lo <= t1.hi && t2.hi < t1.lo) then
      create ~lo:t1.lo ~hi:t2.hi ~size
    else
      invalid_arg "union: missed a case with one range wrapped"
  else if Bv.(t2.lo <= t1.hi || t1.lo <= t2.hi) then
    create_full ~size
  else
    let l = if Bv.(t2.lo < t1.lo) then t2.lo else t1.lo in
    let u = if Bv.(t2.hi > t1.hi) then t2.hi else t1.hi in
    create ~lo:l ~hi:u ~size

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
      create ~lo ~hi:(Bv.setbit Bv.zero t.size (Bv.modulus size)) ~size
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
  if t.size = size then t
  else if t.size < size then
    invalid_argf
      "trunc: `size` %d is not strictly less than `size t` %d"
      size t.size ()
  else if is_empty t then
    create_empty ~size
  else if is_full t then
    create_full ~size
  else with_return @@ fun {return} ->
    let u = ref @@ create_empty ~size
    and ud = ref t.hi 
    and ld = ref t.lo 
    and m = Bv.modulus t.size in
    if is_wrapped_hi t then begin
      if Bv.active_bits t.hi t.size > size then
        return @@ create_full ~size
      else if Bv.cto t.hi t.size = size then
        return @@ create_full ~size
      else
        let lo = Bv.max_unsigned_value size in
        let hi = Bv.extract t.hi ~hi:(size - 1) ~lo:0 in
        u := create ~lo ~hi ~size;
        ud := Bv.(ones mod m);
        if Bv.(t.lo = !ud) then return !u
    end;
    if Bv.active_bits !ld t.size > size then begin
      let bs = Bv.bits_set_from t.size size in
      let adj = Bv.((!ld land bs) mod m) in
      ld := Bv.((!ld - adj) mod m);
      ud := Bv.((!ud - adj) mod m)
    end;
    let udw = Bv.active_bits !ud t.size in
    if udw <= size then
      let lo = Bv.extract !ld ~hi:(size - 1) ~lo:0 in
      let hi = Bv.extract !ud ~hi:(size - 1) ~lo:0 in
      let t' = create ~lo ~hi ~size in
      union t' !u
    else if udw = size + 1 then
      let ud = Bv.clrbit !ud size m in
      if Bv.(ud < !ld) then
        let lo = Bv.extract !ld ~hi:(size - 1) ~lo:0 in
        let hi = Bv.extract ud ~hi:(size - 1) ~lo:0 in
        let t' = create ~lo ~hi ~size in
        union t' !u
      else create_full ~size
    else create_full ~size

let add t1 t2 =
  if t1.size <> t2.size then
    invalid_arg "add: sizes must be equal";
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
      if is_size_strictly_smaller_than x t1
      || is_size_strictly_smaller_than x t2
      then create_full ~size
      else x

let sub t1 t2 =
  if t1.size <> t2.size then
    invalid_arg "sub: sizes must be equal";
  let size = t1.size in
  if is_empty t1 || is_empty t2 then
    create_empty ~size
  else if is_full t1 || is_full t2 then
    create_full ~size
  else
    let module B = (val Bv.modular size) in
    let lo = B.(t1.lo - t2.hi + one) in
    let hi = B.(t1.hi - t2.lo) in
    if Bv.(lo = hi)
    then create_full ~size
    else
      let x = create ~lo ~hi ~size in
      if is_size_strictly_smaller_than x t1
      || is_size_strictly_smaller_than x t2
      then create_full ~size
      else x

let mul_single t1 t2 =
  let size = t1.size in
  match single_of t1 with
  | Some s when Bv.(s = one) -> Some t2
  | Some s when Bv.(s = (ones mod modulus size)) ->
    Some (sub (create_single ~value:Bv.zero ~size) t2)
  | _ -> None

let mul t1 t2 =
  if t1.size <> t2.size then
    invalid_arg "mul: sizes must be equal";
  let size = t1.size in
  if is_empty t1 || is_empty t2 then
    create_empty ~size
  else match mul_single t1 t2 with
    | Some t -> t
    | None -> match mul_single t2 t1 with
      | Some t -> t
      | None ->
        let s2 = size * 2 in
        let module B = (val Bv.modular size) in
        let module B2 = (val Bv.modular s2) in
        let min1 = unsigned_min t1 in
        let max1 = unsigned_max t1 in
        let min2 = unsigned_min t2 in
        let max2 = unsigned_max t2 in
        let result = create
            ~lo:B2.(min1 * min2)
            ~hi:B2.(max1 * max2 + one)
            ~size:s2 in
        let ur = trunc result ~size in
        let m = Bv.modulus size in
        if not (is_wrapped_hi ur) &&
           (not Bv.(msb ur.hi mod m) || Bv.(ur.hi = min_signed_value size))
        then ur
        else
          let min1 = Bv.sext (signed_min t1) size s2 in
          let max1 = Bv.sext (signed_max t1) size s2 in
          let min2 = Bv.sext (signed_min t2) size s2 in
          let max2 = Bv.sext (signed_max t2) size s2 in
          let p = B2.[|
              min1 * min2;
              min1 * max2;
              max1 * min2;
              max1 * max2;
            |] in
          let compare x y = Bv.signed_compare x y s2 in
          let lo = Array.min_elt p ~compare in
          let hi = Array.max_elt p ~compare in
          let lo, hi = match lo, hi with
            | None, _ | _, None -> assert false
            | Some lo, Some hi -> lo, B2.succ hi in
          let result = create ~lo ~hi ~size:s2 in
          let sr = trunc result ~size in
          if is_size_strictly_smaller_than ur sr then ur else sr

let smax t1 t2 =
  if t1.size <> t2.size then
    invalid_arg "smax: sizes must be equal";
  let size = t1.size in
  if is_empty t1 || is_empty t2 then
    create_empty ~size
  else
    let m = Bv.modulus size in
    let min1 = signed_min t1 in
    let max1 = signed_max t1 in
    let min2 = signed_min t2 in
    let max2 = signed_max t2 in
    let lo = if Bv.signed_compare min1 min2 size > 0 then min1 else min2 in
    let hi = if Bv.signed_compare max1 max2 size > 0 then max1 else max2 in
    let hi = Bv.(succ hi mod m) in
    create_non_empty ~lo ~hi ~size

let umax t1 t2 =
  if t1.size <> t2.size then
    invalid_arg "umax: sizes must be equal";
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
    invalid_arg "smin: sizes must be equal";
  let size = t1.size in
  if is_empty t1 || is_empty t2 then
    create_empty ~size
  else
    let m = Bv.modulus size in
    let min1 = signed_min t1 in
    let max1 = signed_max t1 in
    let min2 = signed_min t2 in
    let max2 = signed_max t2 in
    let lo = if Bv.signed_compare min1 min2 size < 0 then min1 else min2 in
    let hi = if Bv.signed_compare max1 max2 size < 0 then max1 else max2 in
    let hi = Bv.(succ hi mod m) in
    create_non_empty ~lo ~hi ~size

let umin t1 t2 =
  if t1.size <> t2.size then
    invalid_arg "umin: sizes must be equal";
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
    invalid_arg "udiv: sizes must be equal";
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
  let size = t1.size in
  if size <> t2.size then
    invalid_arg "sdiv: sizes must be equal";
  if is_empty t1 then t1
  else if is_empty t2 then t2
  else
    let l1 = signed_min t1 and h1 = signed_max t1
    and l2 = signed_min t2 and h2 = signed_max t2 in
    (* Check for 0 in the denominator. *)
    if Bv.signed_compare l2 Bv.zero size <= 0 &&
       Bv.signed_compare Bv.zero h2 size <= 0
    then create_full ~size
    else
      let module B = (val Bv.modular size) in
      (* Check for overflow. *)
      let sm = Bv.min_signed_value size in
      if contains_value t1 sm && contains_value t2 B.ones
      then create_full ~size
      else
        (* Four quadrants. *)
        let qs = B.[|
            l1 /$ l2;
            l1 /$ h2;
            h1 /$ l2;
            h1 /$ h2;
          |] in
        let compare x y = Bv.signed_compare x y size in
        let lo = Array.min_elt qs ~compare in
        let hi = Array.max_elt qs ~compare in
        match lo, hi with
        | None, _ | _, None -> assert false
        | Some lo, Some hi ->
          create_non_empty ~lo ~hi:(B.succ hi) ~size

let urem t1 t2 =
  if t1.size <> t2.size then
    invalid_arg "urem: sizes must be equal";
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
  let smv = Bv.min_signed_value size in
  let module B = (val Bv.modular size) in
  if is_empty t then t
  else if is_sign_wrapped t then
    let lo =
      if Bv.signed_compare t.hi B.zero size > 0 ||
         Bv.signed_compare t.lo B.zero size <= 0
      then Bv.zero
      else Bv.min t.lo B.(succ (neg t.hi)) in
    if int_min_is_poison
    then create ~lo ~hi:smv ~size
    else create ~lo ~hi:(B.succ smv) ~size
  else with_return @@ fun {return} ->
    let smin = signed_min t and smax = signed_max t in
    let smin =
      if int_min_is_poison && Bv.(smin = smv) then
        if Bv.(smax = smv) then return @@ create_empty ~size
        else B.succ smin
      else smin in
    if not (B.msb smin) then
      create ~lo:smin ~hi:(B.succ smax) ~size
    else if B.msb smax then
      create ~lo:(B.neg smax) ~hi:B.(succ (neg smin)) ~size
    else
      let hi = B.succ @@ Bv.max (B.neg smin) smax in
      create ~lo:Bv.zero ~hi ~size

let srem t1 t2 =
  let size = t1.size in
  if size <> t2.size then invalid_arg "srem: size mismatch";
  if is_empty t1 then t1
  else if is_empty t2 then t2
  else
    let module B = (val Bv.modular size) in
    match single_of t1, single_of t2 with
    | _, Some s2 when Bv.(s2 = zero) ->
      create_empty ~size
    | Some s1, Some s2 ->
      create_single ~size ~value:(Bv.srem' s1 s2 size)
    | _ ->
      let abs_rhs = abs t2 in
      let min_abs_rhs = unsigned_min abs_rhs in
      let max_abs_rhs = unsigned_max abs_rhs in
      if Bv.(max_abs_rhs = zero)
      then create_empty ~size
      else
        let min_abs_rhs = if Bv.(min_abs_rhs = zero)
          then B.succ min_abs_rhs else min_abs_rhs in
        let min_lhs = signed_min t1 in
        let max_lhs = signed_max t1 in
        if not @@ B.msb min_lhs then
          if Bv.(max_lhs < min_abs_rhs) then t1 else
            let u = B.succ @@ Bv.min max_lhs @@ B.pred max_abs_rhs in
            create ~lo:Bv.zero ~hi:u ~size
        else if B.msb max_lhs then
          if Bv.(min_lhs > B.neg min_abs_rhs) then t1 else
            let lo = Bv.max min_lhs @@ B.succ @@ B.neg max_abs_rhs in
            create ~lo ~hi:B.one ~size
        else
          let lo = Bv.max min_lhs @@ B.succ @@ B.neg max_abs_rhs in
          let hi = B.succ @@ Bv.min max_lhs @@ B.pred max_abs_rhs in
          create ~lo ~hi ~size

let lnot t =
  let size = t.size in
  let module B = (val Bv.modular size) in
  if is_empty t then t
  else match single_of t with
    | Some v ->
      create_single ~value:B.(lnot v) ~size:size
    | None when is_wrapped t -> create_full ~size
    | None ->
      let lo1 = unsigned_min t in
      let hi1 = unsigned_max t in
      let lo = B.lnot hi1 in
      let hi = B.(succ (lnot lo1)) in
      create_non_empty ~lo ~hi ~size

let neg t =
  if is_empty t then t
  else sub (create_single ~value:Bv.zero ~size:t.size) t

let logand t1 t2 =
  if t1.size <> t2.size then
    invalid_arg "logand: sizes must be equal";
  let size = t1.size in
  let module B = (val Bv.modular size) in
  if is_empty t1 || is_empty t2
  then create_empty ~size
  else match single_of t1, single_of t2 with
    | Some v1, Some v2 ->
      create_single ~value:B.(v1 land v2) ~size
    | _ ->
      let lo1 = unsigned_min t1 in
      let hi1 = unsigned_max t1 in
      let lo2 = unsigned_min t2 in
      let hi2 = unsigned_max t2 in
      let must1_1 = Bv.must_be_ones lo1 hi1 size in
      let must0_1 = Bv.must_be_zeros lo1 hi1 size in
      let must1_2 = Bv.must_be_ones lo2 hi2 size in
      let must0_2 = Bv.must_be_zeros lo2 hi2 size in
      let must_ones = B.(must1_1 land must1_2) in
      let must_zeros = B.(must0_1 lor must0_2) in
      let lo = must_ones in
      let hi = B.(succ (lnot must_zeros)) in
      create_non_empty ~size ~lo ~hi

let logor t1 t2 =
  if t1.size <> t2.size then
    invalid_arg "logor: sizes must be equal";
  let size = t1.size in
  let module B = (val Bv.modular size) in
  if is_empty t1 || is_empty t2
  then create_empty ~size
  else match single_of t1, single_of t2 with
    | Some v1, Some v2 ->
      create_single ~value:B.(v1 lor v2) ~size
    | _ ->
      let lo1 = unsigned_min t1 in
      let hi1 = unsigned_max t1 in
      let lo2 = unsigned_min t2 in
      let hi2 = unsigned_max t2 in
      let must1_1 = Bv.must_be_ones lo1 hi1 size in
      let must0_1 = Bv.must_be_zeros lo1 hi1 size in
      let must1_2 = Bv.must_be_ones lo2 hi2 size in
      let must0_2 = Bv.must_be_zeros lo2 hi2 size in
      let must_ones = B.(must1_1 lor must1_2) in
      let must_zeros = B.(must0_1 land must0_2) in
      let lo = must_ones in
      let hi = B.(succ (lnot must_zeros)) in
      create_non_empty ~size ~lo ~hi

let logxor t1 t2 =
  if t1.size <> t2.size then
    invalid_arg "logxor: sizes must be equal";
  let size = t1.size in
  let module B = (val Bv.modular size) in
  if is_empty t1 || is_empty t2
  then create_empty ~size
  else match single_of t1, single_of t2 with
    | Some v1, Some v2 ->
      create_single ~value:B.(v1 lxor v2) ~size
    | None, Some v when Bv.(v = max_unsigned_value size) -> lnot t1
    | Some v, None when Bv.(v = max_unsigned_value size) -> lnot t2
    | _ ->
      let lo1 = unsigned_min t1 in
      let hi1 = unsigned_max t1 in
      let lo2 = unsigned_min t2 in
      let hi2 = unsigned_max t2 in
      let must1_1 = Bv.must_be_ones lo1 hi1 size in
      let must0_1 = Bv.must_be_zeros lo1 hi1 size in
      let must1_2 = Bv.must_be_ones lo2 hi2 size in
      let must0_2 = Bv.must_be_zeros lo2 hi2 size in
      let must_ones = B.((must1_1 land must0_2) lor (must0_1 land must1_2)) in
      let must_zeros = B.((must1_1 land must1_2) lor (must0_1 land must0_2)) in
      let lo = must_ones in
      let hi = B.(succ (lnot must_zeros)) in
      create_non_empty ~size ~lo ~hi

let logical_shift_left t1 t2 =
  if t1.size <> t2.size then
    invalid_arg "logical_shift_left: sizes must be equal";
  let size = t1.size in
  let m = Bv.modulus size in
  if is_empty t1 || is_empty t2
  then create_empty ~size
  else
    let max1 = unsigned_max t1 in
    let max2 = unsigned_max t2 in
    if Bv.(max2 = zero) then t1
    else if Bv.(max2 > int (Bv.clz max1 size) mod m) then
      create_full ~size
    else
      let min1 = unsigned_min t1 in
      let min2 = unsigned_min t2 in
      let lo = Bv.((min1 lsl min2) mod m) in
      let hi = Bv.(succ ((max1 lsl max2) mod m) mod m) in
      create ~lo ~hi ~size

let logical_shift_right t1 t2 =
  if t1.size <> t2.size then
    invalid_arg "logical_shift_right: sizes must be equal";
  let size = t1.size in
  let m = Bv.modulus size in
  if is_empty t1 || is_empty t2
  then create_empty ~size
  else
    let max1 = unsigned_max t1 in
    let max2 = unsigned_max t2 in
    let min1 = unsigned_min t1 in
    let min2 = unsigned_min t2 in
    let hi = Bv.(succ ((max1 lsr min2) mod m) mod m) in
    let lo = Bv.((min1 lsr max2) mod m) in
    create ~lo ~hi ~size

let arithmetic_shift_right t1 t2 =
  if t1.size <> t2.size then
    invalid_arg "arithmetic_shift_right: sizes must be equal";
  let size = t1.size in
  let m = Bv.modulus size in
  if is_empty t1 || is_empty t2
  then create_empty ~size
  else
    let max1 = signed_max t1 in
    let max2 = unsigned_max t2 in
    let min1 = signed_min t1 in
    let min2 = unsigned_min t2 in
    let pos_max = Bv.(succ ((max1 asr min2) mod m) mod m) in
    let pos_min = Bv.((min1 asr max2) mod m) in
    let neg_max = Bv.(succ ((max1 asr max2) mod m) mod m) in
    let neg_min = Bv.((min1 asr min2) mod m) in
    let lo, hi =
      if Bv.(signed_compare min1 zero size) >= 0 then
        pos_min, pos_max
      else if Bv.(signed_compare max1 zero size) < 0 then
        neg_min, neg_max
      else neg_min, pos_max in
    create_non_empty ~lo ~hi ~size

let extract t ~hi ~lo =
  let size = t.size in
  if lo < 0 then
    invalid_argf "extract: invalid `lo` bit %d" lo ();
  if hi >= size then
    invalid_argf "extract: invalid `hi` bit %d (must be less than `size`)" hi ();
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
    invalid_arg "umulh: sizes must be equal";
  let size = t1.size in
  let size2 = size * 2 in
  let a = zext t1 ~size:size2 in
  let b = zext t2 ~size:size2 in
  extract (mul a b) ~hi:(size2 - 1) ~lo:size

let mulh t1 t2 =
  if t1.size <> t2.size then
    invalid_arg "mulh: sizes must be equal";
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
    invalid_arg "rotate_left: sizes must be equal";
  let size = t1.size in
  let sh = create_single ~value:Bv.(int size mod modulus size) ~size in
  logor (logical_shift_left t1 t2) (logical_shift_right t1 (sub sh t2))

let rotate_right t1 t2 =
  if t1.size <> t2.size then
    invalid_arg "rotate_right: sizes must be equal";
  let size = t1.size in
  let sh = create_single ~value:Bv.(int size mod modulus size) ~size in
  logor (logical_shift_right t1 t2) (logical_shift_left t1 (sub sh t2))

let clz ?(zero_is_poison = true) t =
  if is_empty t then t else
    let module B = (val Bv.modular t.size) in
    if zero_is_poison && contains_value t Bv.zero then
      let ph0 = Bv.(B.pred t.hi = zero) in
      if Bv.(t.lo = zero) then
        if ph0 then
          create_empty ~size:t.size
        else
          let lo = B.(int (Bv.clz (pred t.hi) t.size)) in
          let hi = B.(int (Int.succ @@ Bv.clz (succ t.lo) t.size)) in
          create ~lo ~hi ~size:t.size
      else if ph0 then
        let hi = B.int (Bv.clz t.lo t.size + 1) in
        create ~lo:Bv.zero ~hi ~size:t.size
      else create ~lo:Bv.zero ~hi:(B.int t.size) ~size:t.size
    else
      let umax = unsigned_max t in
      let umin = unsigned_min t in
      let lo = B.int (Bv.clz umax t.size) in
      let hi = B.int (Bv.clz umin t.size + 1) in
      create_non_empty ~lo ~hi ~size:t.size

let ctz_range lo hi size =
  if is_wrapped @@ create ~lo ~hi ~size then
    invalid_argf "ctz_range: [%s, %s):%d is wrapped"
      (Bv.to_string lo) (Bv.to_string hi) size ();
  if Bv.(lo = hi) then
    invalid_arg "ctz_range: `lo` and `hi` cannot be equal";
  let module B = (val Bv.modular size) in
  if Bv.(B.succ lo = hi) then
    let value = B.int (Bv.ctz lo size) in
    create_single ~value ~size
  else if Bv.(lo = zero) then
    create ~lo:Bv.zero ~hi:(B.int (size + 1)) ~size
  else
    let len = Bv.clz B.(lo lxor pred hi) size in
    let hi = B.int (max (size - len - 1) (Bv.ctz lo size) + 1) in
    create ~size ~lo:Bv.zero ~hi

let ctz ?(zero_is_poison = true) t =
  if is_empty t then t else
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
      (Bv.to_string lo) (Bv.to_string hi) size ();
  if Bv.(lo = hi) then
    invalid_arg "popcnt_range: `lo` and `hi` cannot be equal";
  let module B = (val Bv.modular size) in
  if Bv.(B.succ lo = hi) then
    let value = B.int (Bv.popcnt lo) in
    create_single ~value ~size
  else
    let ph = B.pred hi in
    let len = Bv.clz B.(lo lxor ph) size in
    let lhi =
      if len = 0 then Bv.zero
      else Bv.extract ~hi:(size - 1) ~lo:(size - len) lo in
    let cnt = Bv.popcnt lhi in
    let bmin = cnt + if Bv.ctz lo size < size - len then 1 else 0 in
    let bmax =
      cnt + (size - len) -
      if Bv.cto ph size < size - len then 1 else 0 in
    create ~size ~lo:(B.int bmin) ~hi:(B.int (bmax + 1))

let popcnt t =
  if is_empty t then t else
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
          ~lo:(B.int (Bv.clo t.lo t.size))
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

let inverse_predicate = function
  | EQ -> NE
  | NE -> EQ
  | LT -> GE
  | GE -> LT
  | LE -> GT
  | GT -> LE
  | SLT -> SGE
  | SGE -> SLT
  | SLE -> SGT
  | SGT -> SLE

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

let satisfying_icmp_region i p =
  inverse @@ allowed_icmp_region i @@ inverse_predicate p

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
