(** Allen's Interval Algebra, extended to relate a {e point} with an interval.

    This is the point-versus-interval companion to {!Allen_interval_algebra}
    (which relates two intervals). Both share the same input signature
    {!Allen_interval_algebra.S}.
*)

open Core

type t =
  | Before
  | Starts
  | During
  | Finishes
  | After
[@@deriving compare, equal, sexp]

let pp ppf t = Format.fprintf ppf "%a" Sexp.pp @@ sexp_of_t t

(** The input interval type (shared with {!Allen_interval_algebra}). *)
module type S = Allen_interval_algebra.S

(** Create the relations between a point and an interval. *)
module Make(M : S) = struct
  open M

  let before   p i = p < lo i [@@inline]
  let starts   p i = p = lo i [@@inline]
  let during   p i = p > lo i && p < hi i [@@inline]
  let finishes p i = p = hi i [@@inline]
  let after    p i = p > hi i [@@inline]

  (** Relates a point [p] with an interval [i].

      Requires the interval invariant [lo i < hi i].
  *)
  let relate p i =
    if before p i then Before
    else if starts p i then Starts
    else if during p i then During
    else if finishes p i then Finishes
    else After
end
