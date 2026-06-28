open Core
open Regular.Std

module W = Int

let bpw = Sys.int_size_in_bits
let () = assert (W.num_bits = bpw)

type key = int

(* Invariants:

   - the top word is always nonzero (so no trailing zero words)
   - the empty set has length 0
*)
type t = W.t Vec.t

(* Word-level helpers. *)
let is_wzero w = W.equal w W.zero [@@inline]
let bit b = W.shift_left W.one b [@@inline]
let testbit w b = not (is_wzero (W.bit_and w (bit b))) [@@inline]
let poplsb w = W.bit_and w (W.pred w) [@@inline]
let lowest_bit w = W.ctz w [@@inline]
let highest_bit w = bpw - 1 - W.clz w [@@inline]

let create ?(capacity = 1) () : t = Vec.create ~capacity ()
let copy t = Vec.copy t
let is_empty t = Vec.is_empty t
let clear t = Vec.clear t

(* Drop trailing zero words to restore the canonical form. *)
let trim t =
  let continue = ref true in
  while !continue do
    let n = Vec.length t in
    if n > 0 && is_wzero (Vec.unsafe_get t (n - 1))
    then ignore (Vec.pop_exn t : W.t)
    else continue := false
  done

(* Grow `t` so that word index `w` is valid, padding with zeros. *)
let ensure_word t w =
  while Vec.length t <= w do Vec.push t W.zero done

let mem t k =
  let w = k / bpw in
  w < Vec.length t && testbit (Vec.unsafe_get t w) (k mod bpw)
[@@inline]

let add t k =
  let w = k / bpw and b = k mod bpw in
  ensure_word t w;
  Vec.unsafe_set t w (W.bit_or (Vec.unsafe_get t w) (bit b))

let remove t k =
  let w = k / bpw in
  if w < Vec.length t then
    let nv =
      W.bit_and
        (Vec.unsafe_get t w)
        (W.bit_not (bit (k mod bpw))) in
    Vec.unsafe_set t w nv;
    if is_wzero nv && w = Vec.length t - 1 then trim t

let singleton k =
  let t = create () in
  add t k;
  t

let init n =
  let t = create ~capacity:(max 1 (n / bpw + 1)) () in
  if n > 0 then begin
    let w = n / bpw and b = n mod bpw in
    for _ = 1 to w do Vec.push t W.minus_one done; (* full words *)
    if b <> 0 then Vec.push t (W.pred (bit b))     (* low `b` bits *)
  end;
  t

(* a := a ∪ b *)
let union a b =
  let lb = Vec.length b in
  while Vec.length a < lb do Vec.push a W.zero done;
  for i = 0 to lb - 1 do
    Vec.unsafe_set a i
      (W.bit_or
         (Vec.unsafe_get a i)
         (Vec.unsafe_get b i))
  done

(* a := a ∩ b *)
let inter a b =
  let n = Int.min (Vec.length a) (Vec.length b) in
  for i = 0 to n - 1 do
    Vec.unsafe_set a i
      (W.bit_and
         (Vec.unsafe_get a i)
         (Vec.unsafe_get b i))
  done;
  while Vec.length a > n do ignore (Vec.pop_exn a : W.t) done;
  trim a

(* a := a ∖ b *)
let diff a b =
  let n = Int.min (Vec.length a) (Vec.length b) in
  for i = 0 to n - 1 do
    Vec.unsafe_set a i
      (W.bit_and
         (Vec.unsafe_get a i)
         (W.bit_not (Vec.unsafe_get b i)))
  done;
  trim a

(* Index of the first nonzero word.

   pre: the set is nonempty
*)
let first_nonzero t =
  let i = ref 0 in
  while is_wzero (Vec.unsafe_get t !i) do incr i done;
  !i

let min_elt_exn t =
  if Vec.is_empty t then invalid_arg "Bitset.min_elt_exn: empty set";
  let i = first_nonzero t in
  i * bpw + lowest_bit (Vec.unsafe_get t i)

let max_elt_exn t =
  let n = Vec.length t in
  if n = 0 then invalid_arg "Bitset.max_elt_exn: empty set";
  let i = n - 1 in (* canonical: top word is nonzero *)
  i * bpw + highest_bit (Vec.unsafe_get t i)

let min_elt t = if Vec.is_empty t then None else Some (min_elt_exn t)
let max_elt t = if Vec.is_empty t then None else Some (max_elt_exn t)

let pop_min_exn t =
  if Vec.is_empty t then invalid_arg "Bitset.pop_min_exn: empty set";
  let i = first_nonzero t in
  let w = Vec.unsafe_get t i in
  let w' = poplsb w in
  Vec.unsafe_set t i w';
  if is_wzero w' && i = Vec.length t - 1 then trim t;
  i * bpw + lowest_bit w

let pop_max_exn t =
  let n = Vec.length t in
  if n = 0 then invalid_arg "Bitset.pop_max_exn: empty set";
  let i = n - 1 in
  let w = Vec.unsafe_get t i in
  let b = highest_bit w in
  Vec.unsafe_set t i (W.bit_and w (W.bit_not (bit b)));
  trim t; (* the top word may now be zero *)
  i * bpw + b

let enum ?(rev = false) t =
  let open Seq.Generator in
  let len = Vec.length t in
  let rec fwd i w =
    if not (is_wzero w) then
      let b = lowest_bit w in
      yield (i * bpw + b) >>= fun () ->
      fwd i (poplsb w)
    else if i + 1 < len
    then fwd (i + 1) (Vec.unsafe_get t (i + 1))
    else return () in
  let rec bwd i w =
    if not (is_wzero w) then
      let b = highest_bit w in
      yield (i * bpw + b) >>= fun () ->
      bwd i (W.bit_and w (W.bit_not (bit b)))
    else if i - 1 >= 0
    then bwd (i - 1) (Vec.unsafe_get t (i - 1))
    else return () in
  run @@ if len = 0 then return ()
  else if rev then bwd (len - 1) (Vec.unsafe_get t (len - 1))
  else fwd 0 (Vec.unsafe_get t 0)

let fold ?(rev = false) t ~init ~f =
  let len = Vec.length t in
  let acc = ref init in
  if rev then
    for i = len - 1 downto 0 do
      let w = ref (Vec.unsafe_get t i) in
      while not (is_wzero !w) do
        let b = highest_bit !w in
        acc := f !acc (i * bpw + b);
        w := W.bit_and !w (W.bit_not (bit b))
      done
    done
  else
    for i = 0 to len - 1 do
      let w = ref (Vec.unsafe_get t i) in
      while not (is_wzero !w) do
        let b = lowest_bit !w in
        acc := f !acc (i * bpw + b);
        w := poplsb !w
      done
    done;
  !acc

let iter ?(rev = false) t ~f =
  let len = Vec.length t in
  if rev then
    for i = len - 1 downto 0 do
      let w = ref (Vec.unsafe_get t i) in
      while not (is_wzero !w) do
        let b = highest_bit !w in
        f (i * bpw + b);
        w := W.bit_and !w (W.bit_not (bit b))
      done
    done
  else
    for i = 0 to len - 1 do
      let w = ref (Vec.unsafe_get t i) in
      while not (is_wzero !w) do
        let b = lowest_bit !w in
        f (i * bpw + b);
        w := poplsb !w
      done
    done

let for_all t ~f =
  let len = Vec.length t in
  let rec go i w =
    if not (is_wzero w) then
      let b = lowest_bit w in
      f (i * bpw + b) && go i (poplsb w)
    else i + 1 >= len || go (i + 1) (Vec.unsafe_get t (i + 1)) in
  len = 0 || go 0 (Vec.unsafe_get t 0)

(* The canonical form makes structural equality and comparison agree
   with set semantics. *)
let equal a b =
  let n = Vec.length a in
  let rec go i =
    i >= n || begin
      let wa = Vec.unsafe_get a i
      and wb = Vec.unsafe_get b i in
      W.equal wa wb && go (i + 1)
    end in
  n = Vec.length b && go 0

let compare a b =
  let la = Vec.length a and lb = Vec.length b in
  match Int.compare la lb with
  | 0 ->
    let rec go i =
      if i >= la then 0 else
        let wa = Vec.unsafe_get a i
        and wb = Vec.unsafe_get b i in
        match W.compare wa wb with
        | 0 -> go (i + 1)
        | c -> c in
    go 0
  | c -> c

let sexp_of_t t = Seq.to_list (enum t) |> [%sexp_of: int list]

let t_of_sexp sexp =
  let t = create () in
  [%of_sexp: int list] sexp |> List.iter ~f:(add t);
  t
