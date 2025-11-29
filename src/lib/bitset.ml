open Core
open Regular.Std
open Bitset_intf

module Make(K : Key) = struct
  type t = Z.t [@@deriving compare, equal]

  let sexp_of_t t = Sexp.Atom (Z.to_string t)

  let t_of_sexp = function
    | Sexp.Atom s -> Z.of_string s
    | x ->
      let exn = Failure "Bitset.t_of_sexp: atom needed" in
      raise @@ Sexplib.Conv.Of_sexp_error (exn, x)

  let empty = Z.zero
  let is_empty t = Z.equal t empty [@@inline]
  let singleton k = Z.(one lsl K.to_int k) [@@inline]
  let union = Z.logor
  let inter = Z.logand
  let set t k = union t @@ singleton k [@@inline]
  let clear t k = inter t @@ Z.lognot @@ singleton k [@@inline]
  let mem t k = Z.testbit t @@ K.to_int k [@@inline]
  let init n = Z.(pred (one lsl n)) [@@inline]

  let min_elt_exn t =
    if is_empty t then
      invalid_arg "Bitset.min_elt_exn: empty set";
    K.of_int @@ Z.trailing_zeros t

  let min_elt t = if is_empty t then None
    else Some (K.of_int @@ Z.trailing_zeros t)

  let enum =
    let open Seq.Generator in
    let pop_min t = Z.(t land pred t) in
    let rec go t =
      if is_empty t then return () else
        let i = min_elt_exn t in
        yield i >>= fun () ->
        go (pop_min t) in
    fun t -> run @@ go t
end

module Id = Make(Int)
