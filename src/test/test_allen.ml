open Core
open Cgen
open Allen_interval_algebra

module Seq = Sequence
module Q = Quickcheck
module G = Q.Generator
module S = Q.Shrinker
module O = Q.Observer
module T = Base_quickcheck.Test

type range = {
  lo : int;
  hi : int;
} [@@deriving sexp]

let (--) lo hi = {lo; hi}

module R = struct
  type point = int
  type t = range
  let lo t = t.lo
  let hi t = t.hi
  include Int.Replace_polymorphic_compare
end

module A = Make(R)

let rels a b = A.[|
    before a b;
    meets a b;
    overlaps a b;
    finished_by a b;
    contains a b;
    starts a b;
    equal a b;
    started_by a b;
    during a b;
    finishes a b;
    overlapped_by a b;
    met_by a b;
    after a b;
  |]

let range_ok r =
  r.lo >= -500 && r.lo < r.hi && r.hi <= 500

let gen_range =
  G.map2 Int.quickcheck_generator Int.quickcheck_generator ~f:((--)) |>
  G.filter ~f:range_ok

let obs_range =
  O.(unmap
       (tuple2
          Int.quickcheck_observer
          Int.quickcheck_observer))
    ~f:(fun {lo; hi} -> lo, hi)

let shr_range = S.create @@ fun {lo; hi} ->
  S.(shrink
       (tuple2
          Int.quickcheck_shrinker
          Int.quickcheck_shrinker))
    (lo, hi) |>
  Seq.filter_map ~f:(fun (lo, hi) ->
      let r = {lo; hi} in
      if range_ok r then Some r else None)

let gen_pair = G.map2 gen_range gen_range ~f:Tuple2.create

module Pair = struct
  type t = range * range [@@deriving sexp]
  let quickcheck_generator = gen_pair
  let quickcheck_observer = O.tuple2 obs_range obs_range
  let quickcheck_shrinker = S.tuple2 shr_range shr_range
end

let%test_unit "valid allen relation" =
  T.run_exn (module Pair) ~f:(fun (a, b) ->
      match A.relate a b with
      | Before | Meets | Overlaps | Finished_by
      | Contains | Starts | Equal | Started_by
      | During | Finishes | Overlapped_by | Met_by | After -> ())

let%test_unit "converse law" =
  T.run_exn (module Pair) ~f:(fun (a, b) ->
      let r_ab = A.relate a b in
      let r_ba = A.relate b a in
      let r_ab' = converse r_ab in
      assert (equal r_ab' r_ba))

let%test_unit "reflexive: only equal when identical" =
  T.run_exn (module Pair) ~f:(fun (a, b) ->
      if a.lo = b.lo && a.hi = b.hi then
        assert (equal (A.relate a b) Equal)
      else
        assert (not (equal (A.relate a b) Equal)))

let%test_unit "exclusive relation" =
  T.run_exn (module Pair) ~f:(fun (a, b) ->
      assert (Array.count (rels a b) ~f:Fn.id = 1))

let%test_unit "converse table is correct" =
  T.run_exn (module Pair) ~f:(fun (a, b) ->
      let r = A.relate a b in
      let r' = A.relate b a in
      assert (equal (converse r) r'))

let%test_unit "monotonicity: if a.before b, shrinking b cannot make a.after b" =
  T.run_exn (module Pair) ~f:(fun (a, b) ->
      if equal (A.relate a b) Before then
        let b' = {b with lo = b.lo - 1} in
        let r = A.relate a b' in
        assert (not (equal r After)))

let%test_unit "same start implies one of {Starts, Equal, Started_by}" =
  T.run_exn (module Pair) ~f:(fun (a, b) ->
      if a.lo = b.lo then match A.relate a b with
        | Starts | Equal | Started_by -> ()
        | _ -> assert false)

let%test_unit "same end implies one of {Finishes, Equal, Finished_by}" =
  T.run_exn (module Pair) ~f:(fun (a, b) ->
      if a.hi = b.hi then match A.relate a b with
        | Finishes | Equal | Finished_by -> ()
        | _ -> assert false)

let%test_unit "symmetry class preserved under endpoint translation" =
  T.run_exn (module Pair) ~f:(fun (a, b) ->
      let shift = 5 in
      let a2 = {lo = a.lo + shift; hi = a.hi + shift} in
      let b2 = {lo = b.lo + shift; hi = b.hi + shift} in
      assert (equal (A.relate a b) (A.relate a2 b2)))

let check expect a b =
  let r = A.relate a b in
  assert (equal expect r);
  let r' = A.relate b a in
  assert (equal (converse expect) r')

let%test_unit "rel: before" = check Before (1--3) (5--7)
let%test_unit "rel: meets" = check Meets (1--3) (3--8)
let%test_unit "rel: overlaps" = check Overlaps (1--5) (3--8)
let%test_unit "rel: finished_by" = check Finished_by (1--10) (4--10)
let%test_unit "rel: contains" = check Contains (1--10) (3--7)
let%test_unit "rel: starts" = check Starts (1--3) (1--10)
let%test_unit "rel: equal" = check Equal (2--7) (2--7)
let%test_unit "rel: started_by" = check Started_by (1--10) (1--3)
let%test_unit "rel: during" = check During (4--6) (1--10)
let%test_unit "rel: finishes" = check Finishes (4--10) (1--10)
let%test_unit "rel: overlapped_by" = check Overlapped_by (5--10) (1--7)
let%test_unit "rel: met_by" = check Met_by (10--15) (5--10)
let%test_unit "rel: after" = check After (10--15) (1--7)
