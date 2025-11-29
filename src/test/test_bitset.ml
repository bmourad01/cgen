open Core
open Cgen

module Seq = Sequence
module B = Bitset.Id
module Q = Quickcheck
module G = Q.Generator
module S = Q.Shrinker
module O = Q.Observer
module T = Base_quickcheck.Test

(* Keys must be positive, but if we include really large ones
   in our tests then we might OOM. *)
let key_ok i = i >= 0 && i <= 2000
let gen_key = Int.quickcheck_generator |> G.filter ~f:key_ok

let gen_set =
  G.(list (tuple2 gen_key bool)) |> G.map ~f:(fun bits ->
      List.fold bits ~init:B.empty ~f:(fun acc (k, on) ->
          if on then B.set acc k else acc))

let shr_set = S.create @@ fun s ->
  B.enum s |> Seq.map ~f:(B.clear s)

let obs_set = O.unmap [%observer : int list]
    ~f:(Fn.compose Seq.to_list B.enum)

module Single = struct
  type t = B.t [@@deriving sexp]
  let quickcheck_generator = gen_set
  let quickcheck_observer = obs_set
  let quickcheck_shrinker = shr_set
end

module Pair = struct
  type t = B.t * B.t [@@deriving sexp]
  let quickcheck_generator = G.tuple2 gen_set gen_set
  let quickcheck_observer = O.tuple2 obs_set obs_set
  let quickcheck_shrinker = S.tuple2 shr_set shr_set
end

module Triple = struct
  type t = B.t * B.t * B.t [@@deriving sexp]
  let quickcheck_generator = G.tuple3 gen_set gen_set gen_set
  let quickcheck_observer = O.tuple3 obs_set obs_set obs_set
  let quickcheck_shrinker = S.tuple3 shr_set shr_set shr_set
end

module Key = struct
  type t = int [@@deriving sexp]
  let quickcheck_generator = gen_key
  let quickcheck_observer = [%observer : int]
  let quickcheck_shrinker = S.filter Int.quickcheck_shrinker ~f:key_ok
end

module With_key = struct
  type t = B.t * int [@@deriving sexp]
  let quickcheck_generator = G.tuple2 gen_set gen_key
  let quickcheck_observer = O.tuple2 obs_set [%observer : int]
  let quickcheck_shrinker = S.tuple2 shr_set [%shrinker : int]
end

let%test_unit "union is commutative" =
  T.run_exn (module Pair) ~f:(fun (a, b) ->
      [%test_eq : B.t] (B.union a b) (B.union b a))

let%test_unit "union is associative" =
  T.run_exn (module Triple) ~f:(fun (a, b, c) ->
      [%test_eq : B.t]
        (B.union a (B.union b c))
        (B.union (B.union a b) c))

let%test_unit "inter is commutative" =
  T.run_exn (module Pair) ~f:(fun (a, b) ->
      [%test_eq : B.t] (B.inter a b) (B.inter b a))

let%test_unit "inter is associative" =
  T.run_exn (module Triple) ~f:(fun (a, b, c) ->
      [%test_eq : B.t]
        (B.inter a (B.inter b c))
        (B.inter (B.inter a b) c))

let%test_unit "set / mem consistency" =
  T.run_exn (module With_key) ~f:(fun (s, k) ->
      let s' = B.set s k in
      assert (B.mem s' k))

let%test_unit "clear / mem consistency" =
  T.run_exn (module With_key) ~f:(fun (s, k) ->
      let s' = B.clear s k in
      assert (not (B.mem s' k)))

let%test_unit "singleton has exactly one element" =
  T.run_exn (module Key) ~f:(fun k ->
      [%test_result : int list]
        (Seq.to_list (B.enum (B.singleton k)))
        ~expect:[k])

let%test_unit "init n = [0..n-1]" =
  T.run_exn (module Key) ~f:(fun n ->
      [%test_result : int list]
        (Seq.to_list (B.enum (B.init n)))
        ~expect:(List.init n ~f:Fn.id))

let%test_unit "min_elt matches smallest element in enum" =
  T.run_exn (module Single) ~f:(fun s ->
      match B.min_elt s with
      | None ->
        [%test_eq : int list] (Seq.to_list (B.enum s)) []
      | Some k ->
        let hd = List.hd_exn (Seq.to_list (B.enum s)) in
        [%test_eq : int] k hd)
