open Core
open Regular.Std

type key = int
type t = Z.t [@@deriving compare, equal]

let sexp_of_t t = Sexp.Atom (Z.to_string t)

let t_of_sexp = function
  | Sexp.Atom s -> Z.of_string s
  | x ->
    let exn = Failure "Bitset.t_of_sexp: atom needed" in
    raise @@ Sexplib.Conv.Of_sexp_error (exn, x)

let empty = Z.zero
let is_empty t = Z.equal t empty [@@inline]
let singleton k = Z.(one lsl k) [@@inline]
let union = Z.logor
let inter = Z.logand
let set t k = union t @@ singleton k [@@inline]
let clear t k = inter t @@ Z.lognot @@ singleton k [@@inline]
let mem t k = Z.testbit t k [@@inline]
let init n = Z.(pred (one lsl n)) [@@inline]
let min_elt_unsafe = Z.trailing_zeros
let max_elt_unsafe t = Z.numbits t - 1 [@@inline]

let min_elt_exn t =
  if is_empty t then invalid_arg "Bitset.min_elt_exn: empty set";
  min_elt_unsafe t

let max_elt_exn t =
  if is_empty t then invalid_arg "Bitset.max_elt_exn: empty set";
  max_elt_unsafe t

let min_elt t = if is_empty t then None else Some (min_elt_unsafe t)
let max_elt t = if is_empty t then None else Some (max_elt_unsafe t)

let pop_min t = Z.(t land pred t) [@@inline]

let pop_min_elt_exn t =
  if is_empty t then invalid_arg "Bitset.pop_min_elt_exn: empty set";
  min_elt_unsafe t, pop_min t

let pop_max_elt_exn t =
  if is_empty t then invalid_arg "Bitset.pop_max_elt_exn: empty set";
  let k = max_elt_unsafe t in
  k, clear t k

let pop_min_elt t =
  if is_empty t then None
  else Some (min_elt_unsafe t, pop_min t)

let pop_max_elt t =
  if is_empty t then None else
    let k = max_elt_unsafe t in
    Some (k, clear t k)

let enum =
  let open Seq.Generator in
  let rec go f t = match f t with
    | Some (k, t') -> yield k >>= fun () -> go f t'
    | None -> return () in
  let _ = Z.numbits in
  fun ?(rev = false) t ->
    let f = if rev then pop_max_elt else pop_min_elt in
    run @@ (go[@specialised]) f t

