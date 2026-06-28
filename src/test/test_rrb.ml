open Core

module Q = Quickcheck
module G = Q.Generator
module S = Q.Shrinker
module O = Q.Observer
module T = Base_quickcheck.Test
module Seq = Sequence
module RRB = Cgen_containers.Rrb

type op =
  | Cons of int
  | Snoc of int
  | Append of int list
  | Take of int
  | Drop of int
  | Set of int * int
[@@deriving sexp_of]

let apply_model m = function
  | Cons x -> x :: m
  | Snoc x -> m @ [x]
  | Append xs -> m @ xs
  | Take n -> List.take m n
  | Drop n -> List.drop m n
  | Set (i, _) when i < 0 || i >= List.length m -> m
  | Set (i, x) -> List.mapi m ~f:(fun j y -> if i = j then x else y)

let apply_rrb t = function
  | Cons x -> RRB.cons x t
  | Snoc x -> RRB.snoc t x
  | Append xs -> RRB.append t (RRB.of_list xs)
  | Take n -> RRB.take t n
  | Drop n -> RRB.drop t n
  | Set (i, x) -> RRB.set t i x

let gen_rrb = G.map (G.list Int.quickcheck_generator) ~f:RRB.of_list
let gen_fn = G.fn Int.quickcheck_observer Int.quickcheck_generator

let gen_op = G.weighted_union [
    3., G.map Int.quickcheck_generator ~f:(fun x -> Cons x);
    3., G.map Int.quickcheck_generator ~f:(fun x -> Snoc x);
    2., G.map (G.list Int.quickcheck_generator) ~f:(fun xs -> Append xs);
    1., G.map Int.quickcheck_generator ~f:(fun n -> Take n);
    1., G.map Int.quickcheck_generator ~f:(fun n -> Drop n);
    2., G.map
      (G.tuple2 Int.quickcheck_generator Int.quickcheck_generator)
      ~f:(fun (i, x) -> Set (i, x));
  ]

let shrink_int x = S.shrink Int.quickcheck_shrinker x

let shrink_int_list xs =
  S.shrink (List.quickcheck_shrinker Int.quickcheck_shrinker) xs

let shrink_op = S.create @@ function
  | Cons x -> Seq.map (shrink_int x) ~f:(fun x' -> Cons x')
  | Snoc x -> Seq.map (shrink_int x) ~f:(fun x' -> Snoc x')
  | Append xs -> Seq.map (shrink_int_list xs) ~f:(fun xs' -> Append xs')
  | Take n -> Seq.map (shrink_int n) ~f:(fun n' -> Take n')
  | Drop n -> Seq.map (shrink_int n) ~f:(fun n' -> Drop n')
  | Set (i, x) ->
    let shrink_i = Seq.map (shrink_int i) ~f:(fun i' -> Set (i', x)) in
    let shrink_x = Seq.map (shrink_int x) ~f:(fun x' -> Set (i, x')) in
    Seq.append shrink_i shrink_x

let shrink_rrb = S.map ~f_inverse:RRB.to_list ~f:RRB.of_list
    (List.quickcheck_shrinker Int.quickcheck_shrinker)

module Single = struct
  type t = int RRB.t [@@deriving sexp_of]
  let quickcheck_generator = gen_rrb
  let quickcheck_shrinker = shrink_rrb
end

module Pair = struct
  type t = int RRB.t * int RRB.t [@@deriving sexp_of]
  let quickcheck_generator = G.tuple2 gen_rrb gen_rrb
  let quickcheck_shrinker = S.tuple2 shrink_rrb shrink_rrb
end

module Triple = struct
  type t = int RRB.t * int RRB.t * int RRB.t [@@deriving sexp_of]
  let quickcheck_generator = G.tuple3 gen_rrb gen_rrb gen_rrb
  let quickcheck_shrinker = S.tuple3 shrink_rrb shrink_rrb shrink_rrb
end

module List_ = struct
  type t = int RRB.t list [@@deriving sexp_of]
  let quickcheck_generator = G.list gen_rrb
  let quickcheck_shrinker = List.quickcheck_shrinker shrink_rrb
end

module Int_list = struct
  type t = int list [@@deriving sexp_of]
  let quickcheck_generator = List.quickcheck_generator Int.quickcheck_generator
  let quickcheck_shrinker = List.quickcheck_shrinker Int.quickcheck_shrinker
end

module Ops = struct
  type t = op list [@@deriving sexp_of]
  let quickcheck_generator = List.quickcheck_generator gen_op
  let quickcheck_shrinker = List.quickcheck_shrinker shrink_op
end

let qc1 f = T.run_exn (module Single) ~f
let qc2 f = T.run_exn (module Pair) ~f
let qc3 f = T.run_exn (module Triple) ~f
let qcl f = T.run_exn (module List_) ~f
let qcil f = T.run_exn (module Int_list) ~f
let qco f = T.run_exn (module Ops) ~f

let%test_unit "of_list matches fold+snoc" = qcil @@ fun xs ->
  let v = List.fold xs ~init:RRB.empty ~f:RRB.snoc in
  assert (RRB.equal Int.equal (RRB.of_list xs) v)

let%test_unit "of_list/to_list roundtrip" = qcil @@ fun xs ->
  [%test_eq : int list] xs RRB.(to_list (of_list xs))

let%test_unit "init matches List.init" = qcil @@ fun xs ->
  let arr = Array.of_list xs in
  let n = Array.length arr in
  [%test_eq : int list]
    (RRB.to_list (RRB.init n ~f:(fun i -> arr.(i))))
    xs

let%test_unit "init large multi-level" =
  let n = 100_000 in
  [%test_eq : int]
    (RRB.foldi (RRB.init n ~f:Fn.id) ~init:0 ~f:(fun i acc x ->
         assert (i = x); acc + x))
    ((n * (n - 1)) / 2)

let%test_unit "iter matches to_list" = qc1 @@ fun t ->
  let acc = ref [] in
  RRB.iter t ~f:(fun x -> acc := x :: !acc);
  [%test_eq : int list] (List.rev !acc) (RRB.to_list t)

let%test_unit "iter_rev matches to_list" = qc1 @@ fun t ->
  let acc = ref [] in
  RRB.iter_rev t ~f:(fun x -> acc := x :: !acc);
  [%test_eq : int list] !acc (RRB.to_list t)

let%test_unit "is_empty matches length=0" = qc1 @@ fun t ->
  [%test_eq : bool] (RRB.is_empty t) (RRB.length t = 0)

let%test_unit "filter matches List.filter" = qc1 @@ fun t ->
  let pred x = x % 2 = 0 in
  [%test_eq : int list]
    (RRB.to_list (RRB.filter t ~f:pred))
    (List.filter (RRB.to_list t) ~f:pred)

let%test_unit "exists matches List.exists" = qc1 @@ fun t ->
  let target = Quickcheck.random_value Int.quickcheck_generator in
  [%test_eq : bool]
    (RRB.exists t ~f:(fun x -> x = target))
    (List.exists (RRB.to_list t) ~f:(fun x -> x = target))

let%test_unit "find matches List.find" = qc1 @@ fun t ->
  let pred x = x > 0 in
  [%test_eq : int option]
    (RRB.find t ~f:pred)
    (List.find (RRB.to_list t) ~f:pred)

let%test_unit "of_sequence matches of_list" = qcil @@ fun xs ->
  [%test_eq : int list]
    (RRB.to_list (RRB.of_sequence (Sequence.of_list xs)))
    xs

let%test_unit "length matches list length" = qc1 @@ fun t ->
  let l1 = RRB.length t in
  let l2 = List.length @@ RRB.to_list t in
  [%test_eq : int] l1 l2

let%test_unit "get matches list nth" = qc1 @@ fun t ->
  let xs = RRB.to_list t in
  List.iteri xs ~f:(fun i x ->
      [%test_eq : int] (RRB.get_exn t i) x)

let%test_unit "append matches list append" = qc2 @@ fun (t1, t2) ->
  let lhs = RRB.to_list (RRB.append t1 t2) in
  let rhs = RRB.to_list t1 @ RRB.to_list t2 in
  if not (List.equal Int.equal lhs rhs) then
    raise_s [%sexp "concat mismatch", {
        t1  : int RRB.t;
        t2  : int RRB.t;
        lhs : int list;
        rhs : int list;
      }]

let%test_unit "map matches list map" =
  qc1 @@ fun t ->
  let open RRB in
  let f = Quickcheck.random_value gen_fn in
  let lhs = to_list (map t ~f) in
  let rhs = List.map (to_list t) ~f in
  [%test_eq : int list] lhs rhs

let%test_unit "append empty identity (left)" = qc1 @@ fun t ->
  [%test_eq : int list]
    (RRB.to_list (RRB.append RRB.empty t))
    (RRB.to_list t)

let%test_unit "append empty identity (right)" = qc1 @@ fun t ->
  [%test_eq : int list]
    (RRB.to_list (RRB.append t RRB.empty))
    (RRB.to_list t)

let%test_unit "append is associative" = qc3 @@ fun (a, b, c) ->
  let lhs = RRB.to_list (RRB.append (RRB.append a b) c) in
  let rhs = RRB.to_list (RRB.append a (RRB.append b c)) in
  [%test_eq : int list] lhs rhs

let%test_unit "take/drop roundtrip" = qc1 @@ fun t ->
  let n = RRB.length t / 2 in
  let t' = RRB.append (RRB.take t n) (RRB.drop t n) in
  [%test_eq : int list]
    (RRB.to_list t')
    (RRB.to_list t)

let%test_unit "split_at matches list split" = qc1 @@ fun t ->
  let xs = RRB.to_list t in
  let n = List.length xs / 2 in
  let l1, l2 = List.split_n xs n in
  let t1, t2 = RRB.split_at t n in
  [%test_eq : int list] (RRB.to_list t1) l1;
  [%test_eq : int list] (RRB.to_list t2) l2

let%test_unit "set preserves length" = qc1 @@ fun t ->
  match RRB.length t with
  | 0 -> ()
  | n ->
    let i = n / 2 in
    let t' = RRB.set t i 42 in
    [%test_eq : int] (RRB.length t') n

let%test_unit "update matches list update" = qc1 @@ fun t ->
  match RRB.to_list t with
  | [] -> ()
  | xs ->
    let i = List.length xs / 2 in
    let f x = x + 1 in
    let t' = RRB.update t i ~f in
    let xs' = List.mapi xs ~f:(fun j x -> if j = i then f x else x) in
    [%test_eq : int list] (RRB.to_list t') xs'

let%test_unit "map identity" = qc1 @@ fun t ->
  [%test_eq : int list]
    (RRB.to_list (RRB.map t ~f:Fn.id))
    (RRB.to_list t)

let%test_unit "map composition" = qc1 @@ fun t ->
  let f x = x + 1 in
  let g x = x * 2 in
  let lhs = RRB.to_list (RRB.map (RRB.map t ~f) ~f:g) in
  let rhs = RRB.to_list (RRB.map t ~f:(fun x -> g (f x))) in
  [%test_eq : int list] lhs rhs

let%test_unit "fold equals List.fold" = qc1 @@ fun t ->
  let f acc x = acc + x in
  [%test_eq : int]
    (RRB.fold t ~init:0 ~f)
    (List.fold (RRB.to_list t) ~init:0 ~f)

let%test_unit "foldi index summation" = qc1 @@ fun t ->
  let f i acc _ = acc + i in
  let n = RRB.length t in
  [%test_eq : int]
    (RRB.foldi t ~init:0 ~f)
    ((n * (n - 1)) / 2)

let%test_unit "append many small vectors" = qcl @@ fun ts ->
  let lhs = List.fold ts ~init:RRB.empty ~f:RRB.append |> RRB.to_list in
  let rhs = List.concat_map ts ~f:RRB.to_list in
  [%test_eq : int list] lhs rhs

let%test_unit "state-machine test" = qco @@ fun ops ->
  let rec loop model rrb = function
    | [] -> ()
    | op :: rest ->
      let expect = apply_model model op in
      let rrb' = apply_rrb rrb op in
      let result = RRB.to_list rrb' in
      if not (List.equal Int.equal result expect) then
        raise_s [%sexp "state mismatch", {
            op     : op;
            model  : int list;
            result : int list;
            expect : int list;
          }];
      loop expect rrb' rest in
  loop [] RRB.empty ops

let%test_unit "append linear in depth, not size" =
  let big = RRB.of_list @@ List.init 1_000_000 ~f:Fn.id in
  let small = RRB.singleton 1 in
  ignore (RRB.append big small)

let%test_unit "equal is reflexive" = qc1 @@ fun t ->
  assert (RRB.equal Int.equal t t)

let%test_unit "empty equality" =
  assert (RRB.equal Int.equal RRB.empty RRB.empty)

let%test_unit "equal false when lengths differ" =
  let t1 = RRB.singleton 1 in
  let t2 = RRB.append t1 (RRB.singleton 2) in
  assert (not (RRB.equal Int.equal t1 t2))

let%test_unit "compare zero iff equal" = qc2 @@ fun (t1, t2) ->
  let eq = RRB.equal Int.equal t1 t2 in
  let c = RRB.compare Int.compare t1 t2 in
  if eq then [%test_eq : int] c 0

let%test_unit "compare is lexicographic" =
  let t1 = RRB.of_list [1; 2; 3] in
  let t2 = RRB.of_list [1; 2; 4] in
  assert (RRB.compare Int.compare t1 t2 < 0)

let%test_unit "shorter prefix is smaller" =
  let t1 = RRB.of_list [1; 2] in
  let t2 = RRB.of_list [1; 2; 3] in
  assert (RRB.compare Int.compare t1 t2 < 0)

let%test_unit "equal matches list equal" = qc2 @@ fun (t1, t2) ->
  let lhs = RRB.equal Int.equal t1 t2 in
  let rhs = List.equal Int.equal (RRB.to_list t1) (RRB.to_list t2) in
  [%test_eq : bool] lhs rhs

let cmp2 c1 c2 = c1 = c2 || (c1 < 0 && c2 < 0) || (c1 > 0 && c2 > 0)

let%test_unit "compare matches list compare" = qc2 @@ fun (t1, t2) ->
  let lhs = RRB.compare Int.compare t1 t2 in
  let rhs = List.compare Int.compare (RRB.to_list t1) (RRB.to_list t2) in
  assert (cmp2 lhs rhs)

let%test_unit "equal short-circuits on first mismatch" =
  let t1 = RRB.of_list @@ List.init 1_000_000 ~f:(fun _ -> 0) in
  let t2 = RRB.cons 1 t1 in
  assert (not (RRB.equal Int.equal t1 t2))

let%test_unit "equal preserved by map identity" = qc1 @@ fun t ->
  assert (RRB.equal Int.equal t (RRB.map t ~f:Fn.id))

let%test_unit "compare invariant under normalization" = qc1 @@ fun t ->
  let t' = RRB.append RRB.empty t in
  [%test_eq : int] (RRB.compare Int.compare t t') 0
