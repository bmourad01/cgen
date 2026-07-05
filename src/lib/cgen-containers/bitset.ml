open Core

module W = Int

let bpw = Sys.int_size_in_bits
let () = assert (W.num_bits = bpw)

type key = int

(* A set of small nonnegative integers, stored as a bit-vector of machine
   words.

   Invariants:
   - [words.(i) = 0] for every [i] with [len <= i < Vec.length words]
     (words past the logical extent are zero padding);
   - [len = 0] for the empty set, and [words.(len - 1) <> 0] otherwise
     (canonical form: no logical trailing zero words). This makes [is_empty],
     [max_elt], structural [equal], and [compare] agree with set semantics.
*)
type t = {
  mutable len : int;
  words : W.t Vec.t;
}

(* Word-level helpers. *)
let is_wzero w = W.equal w W.zero [@@inline]
let bit b = W.shift_left W.one b [@@inline]
let testbit w b = not (is_wzero (W.bit_and w (bit b))) [@@inline]
let poplsb w = W.bit_and w (W.pred w) [@@inline]
let lowest_bit w = W.ctz w [@@inline]
let highest_bit w = bpw - 1 - W.clz w [@@inline]

let uget t i = Vec.unsafe_get t.words i [@@inline]
let uset t i w = Vec.unsafe_set t.words i w [@@inline]

let create ?(capacity = 1) () : t = {len = 0; words = Vec.create ~capacity ()}

(* Copy only the logical words so a shrunk set's stale high-water capacity is
   not dragged along. *)
let copy t =
  let words = Vec.create ~capacity:(max 1 t.len) () in
  for i = 0 to t.len - 1 do Vec.push words (Vec.unsafe_get t.words i) done;
  {len = t.len; words}

let cardinality t =
  let n = ref 0 in
  for i = 0 to t.len - 1 do
    n := !n + W.popcount (uget t i)
  done;
  !n

let is_empty t = t.len = 0 [@@inline]

let clear t =
  for i = 0 to t.len - 1 do uset t i W.zero done;
  t.len <- 0

let trim t =
  while t.len > 0 && is_wzero (uget t (t.len - 1)) do
    t.len <- t.len - 1
  done

let ensure_word t w =
  while Vec.length t.words <= w do Vec.push t.words W.zero done
[@@inline]

let mem t k =
  let w = k / bpw in
  w < t.len && testbit (uget t w) (k mod bpw)
[@@inline]

let add t k =
  let w = k / bpw and b = k mod bpw in
  ensure_word t w;
  uset t w (W.bit_or (uget t w) (bit b));
  if w >= t.len then t.len <- w + 1

let remove t k =
  let w = k / bpw in
  if w < t.len then begin
    let nv = W.bit_and (uget t w) (W.bit_not (bit (k mod bpw))) in
    uset t w nv;
    if is_wzero nv && w = t.len - 1 then trim t
  end

let singleton k =
  let t = create () in
  add t k;
  t

let init n =
  let t = create ~capacity:(max 1 (n / bpw + 1)) () in
  if n > 0 then begin
    let w = n / bpw and b = n mod bpw in
    for _ = 1 to w do Vec.push t.words W.minus_one done; (* full words *)
    if b <> 0 then Vec.push t.words (W.pred (bit b));    (* low `b` bits *)
    t.len <- Vec.length t.words
  end;
  t

(* a := a ∪ b *)
let union a b =
  let lb = b.len in
  if lb > 0 then ensure_word a (lb - 1);
  for i = 0 to lb - 1 do
    uset a i (W.bit_or (uget a i) (uget b i))
  done;
  if lb > a.len then a.len <- lb

(* a := a ∩ b *)
let inter a b =
  let n = Int.min a.len b.len in
  for i = n to a.len - 1 do uset a i W.zero done;
  for i = 0 to n - 1 do
    uset a i (W.bit_and (uget a i) (uget b i))
  done;
  a.len <- n;
  trim a

(* a := a ∖ b *)
let diff a b =
  let n = Int.min a.len b.len in
  for i = 0 to n - 1 do
    uset a i (W.bit_and (uget a i) (W.bit_not (uget b i)))
  done;
  trim a

(* Index of the first nonzero word.

   pre: the set is nonempty
*)
let first_nonzero t =
  let i = ref 0 in
  while is_wzero (uget t !i) do incr i done;
  !i

let min_elt_exn t =
  if t.len = 0 then invalid_arg "Bitset.min_elt_exn: empty set";
  let i = first_nonzero t in
  i * bpw + lowest_bit (uget t i)

let max_elt_exn t =
  if t.len = 0 then invalid_arg "Bitset.max_elt_exn: empty set";
  let i = t.len - 1 in (* canonical: top word is nonzero *)
  i * bpw + highest_bit (uget t i)

let min_elt t = if t.len = 0 then None else Some (min_elt_exn t)
let max_elt t = if t.len = 0 then None else Some (max_elt_exn t)

let pop_min_exn t =
  if t.len = 0 then invalid_arg "Bitset.pop_min_exn: empty set";
  let i = first_nonzero t in
  let w = uget t i in
  let w' = poplsb w in
  uset t i w';
  if is_wzero w' && i = t.len - 1 then trim t;
  i * bpw + lowest_bit w

let pop_max_exn t =
  if t.len = 0 then invalid_arg "Bitset.pop_max_exn: empty set";
  let i = t.len - 1 in
  let w = uget t i in
  let b = highest_bit w in
  uset t i (W.bit_and w (W.bit_not (bit b)));
  trim t; (* the top word may now be zero *)
  i * bpw + b

let enum ?(rev = false) t =
  let open Sequence.Generator in
  let len = t.len in
  let rec fwd i w =
    if not (is_wzero w) then
      let b = lowest_bit w in
      yield (i * bpw + b) >>= fun () ->
      fwd i (poplsb w)
    else if i + 1 < len
    then fwd (i + 1) (uget t (i + 1))
    else return () in
  let rec bwd i w =
    if not (is_wzero w) then
      let b = highest_bit w in
      yield (i * bpw + b) >>= fun () ->
      bwd i (W.bit_and w (W.bit_not (bit b)))
    else if i - 1 >= 0
    then bwd (i - 1) (uget t (i - 1))
    else return () in
  run @@ if len = 0 then return ()
  else if rev then bwd (len - 1) (uget t (len - 1))
  else fwd 0 (uget t 0)

let fold ?(rev = false) t ~init ~f =
  let len = t.len in
  let acc = ref init in
  if rev then
    for i = len - 1 downto 0 do
      let w = ref (uget t i) in
      while not (is_wzero !w) do
        let b = highest_bit !w in
        acc := f !acc (i * bpw + b);
        w := W.bit_and !w (W.bit_not (bit b))
      done
    done
  else
    for i = 0 to len - 1 do
      let w = ref (uget t i) in
      while not (is_wzero !w) do
        let b = lowest_bit !w in
        acc := f !acc (i * bpw + b);
        w := poplsb !w
      done
    done;
  !acc

let iter ?(rev = false) t ~f =
  let len = t.len in
  if rev then
    for i = len - 1 downto 0 do
      let w = ref (uget t i) in
      while not (is_wzero !w) do
        let b = highest_bit !w in
        f (i * bpw + b);
        w := W.bit_and !w (W.bit_not (bit b))
      done
    done
  else
    for i = 0 to len - 1 do
      let w = ref (uget t i) in
      while not (is_wzero !w) do
        let b = lowest_bit !w in
        f (i * bpw + b);
        w := poplsb !w
      done
    done

let for_all t ~f =
  let len = t.len in
  let rec go i w =
    if not (is_wzero w) then
      let b = lowest_bit w in
      f (i * bpw + b) && go i (poplsb w)
    else i + 1 >= len || go (i + 1) (uget t (i + 1)) in
  len = 0 || go 0 (uget t 0)

(* The canonical form makes structural equality and comparison agree
   with set semantics. *)
let equal a b =
  let n = a.len in
  let rec go i =
    i >= n || begin
      let wa = uget a i
      and wb = uget b i in
      W.equal wa wb && go (i + 1)
    end in
  n = b.len && go 0

let compare a b =
  let la = a.len and lb = b.len in
  match Int.compare la lb with
  | 0 ->
    let rec go i =
      if i >= la then 0 else
        let wa = uget a i
        and wb = uget b i in
        match W.compare wa wb with
        | 0 -> go (i + 1)
        | c -> c in
    go 0
  | c -> c

let sexp_of_t t = Sequence.to_list (enum t) |> [%sexp_of: int list]

let t_of_sexp sexp =
  let t = create () in
  [%of_sexp: int list] sexp |> List.iter ~f:(add t);
  t
