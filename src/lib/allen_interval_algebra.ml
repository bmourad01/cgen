open Core

(** Allen's Interval Algebra.

    {:https://en.wikipedia.org/wiki/Allen%27s_interval_algebra}
*)

type t =
  | Before
  | Meets
  | Overlaps
  | Finished_by
  | Contains
  | Starts
  | Equal
  | Started_by
  | During
  | Finishes
  | Overlapped_by
  | Met_by
  | After
[@@deriving compare, equal, sexp]

let pp ppf t = Format.fprintf ppf "%a" Sexp.pp @@ sexp_of_t t

(** Returns the converse of the relation. *)
let converse = function
  | Before -> After
  | After -> Before
  | Meets -> Met_by
  | Met_by -> Meets
  | Overlaps -> Overlapped_by
  | Overlapped_by -> Overlaps
  | Starts -> Started_by
  | Started_by -> Starts
  | Finishes -> Finished_by
  | Finished_by -> Finishes
  | During -> Contains
  | Contains -> During
  | Equal -> Equal

(** The input interval type. *)
module type S = sig
  (** A point in the interval. *)
  type point

  (** An inclusive interval. *)
  type t

  (** The lower-bound of the interval. *)
  val lo : t -> point

  (** The upper-bound of the interval. *)
  val hi : t -> point

  include Base.Comparisons.Infix with type t := point
end

(** Create the relations for an interval type. *)
module Make(M : S) = struct
  open M

  let before a b        = hi a < lo b [@@inline]
  let meets a b         = hi a = lo b [@@inline]
  let overlaps a b      = lo a < lo b && hi a > lo b && hi a < hi b [@@inline]
  let finished_by a b   = lo a < lo b && hi a = hi b [@@inline]
  let contains a b      = lo a < lo b && hi a > hi b [@@inline]
  let starts a b        = lo a = lo b && hi a < hi b [@@inline]
  let equal a b         = lo a = lo b && hi a = hi b [@@inline]
  let started_by a b    = lo a = lo b && hi a > hi b [@@inline]
  let during a b        = lo a > lo b && hi a < hi b [@@inline]
  let finishes a b      = lo a > lo b && hi a = hi b [@@inline]
  let overlapped_by a b = lo a > lo b && lo a < hi b && hi a > hi b [@@inline]
  let met_by a b        = lo a = hi b [@@inline]
  let after a b         = lo a > hi b [@@inline]

  (** Relates two intervals. *)
  let relate a b =
    if before a b then Before
    else if meets a b then Meets
    else if overlaps a b then Overlaps
    else if finished_by a b then Finished_by
    else if contains a b then Contains
    else if starts a b then Starts
    else if equal a b then Equal
    else if started_by a b then Started_by
    else if during a b then During
    else if finishes a b then Finishes
    else if overlapped_by a b then Overlapped_by
    else if met_by a b then Met_by
    else After
end
