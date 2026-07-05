open Core

module Q = Quickcheck
module G = Q.Generator
module S = Q.Shrinker
module T = Base_quickcheck.Test
module Ftree = Cgen_containers.Ftree

let tl = Ftree.to_list

let ref_insert xs x i =
  let n = List.length xs in
  let i = Int.max 0 (Int.min i n) in
  List.take xs i @ [x] @ List.drop xs i

let ref_remove xs i =
  let n = List.length xs in
  if i >= 0 && i < n
  then List.take xs i @ List.drop xs (i + 1)
  else xs

let ref_index xs ~f =
  List.findi xs ~f:(fun _ x -> f x) |> Option.map ~f:fst

let ref_next xs ~f = match ref_index xs ~f with
  | Some j -> List.nth xs (j + 1)
  | None -> None

let ref_prev xs ~f =
  List.foldi xs ~init:None ~f:(fun i acc x ->
      if f x then Some i else acc) |> function
  | Some j -> List.nth xs (j - 1)
  | None -> None

let raises f = try ignore (f ()); false with _ -> true

let gen_ft = G.map (G.list Int.quickcheck_generator) ~f:Ftree.of_list

let shrink_ft =
  S.map ~f_inverse:Ftree.to_list ~f:Ftree.of_list
    (List.quickcheck_shrinker Int.quickcheck_shrinker)

module Single = struct
  type t = int Ftree.t
  let sexp_of_t t = Ftree.sexp_of_t Int.sexp_of_t t
  let quickcheck_generator = gen_ft
  let quickcheck_shrinker = shrink_ft
end

module Pair = struct
  type t = int Ftree.t * int Ftree.t
  let sexp_of_t (a, b) =
    [%sexp_of : Sexp.t * Sexp.t]
      (Ftree.sexp_of_t Int.sexp_of_t a, Ftree.sexp_of_t Int.sexp_of_t b)
  let quickcheck_generator = G.tuple2 gen_ft gen_ft
  let quickcheck_shrinker = S.tuple2 shrink_ft shrink_ft
end

module Triple = struct
  type t = int Ftree.t * int Ftree.t * int Ftree.t
  let sexp_of_t (a, b, c) =
    [%sexp_of : Sexp.t * Sexp.t * Sexp.t]
      (Ftree.sexp_of_t Int.sexp_of_t a,
       Ftree.sexp_of_t Int.sexp_of_t b,
       Ftree.sexp_of_t Int.sexp_of_t c)
  let quickcheck_generator = G.tuple3 gen_ft gen_ft gen_ft
  let quickcheck_shrinker = S.tuple3 shrink_ft shrink_ft shrink_ft
end

module Int_list = struct
  type t = int list [@@deriving sexp_of]
  let quickcheck_generator = List.quickcheck_generator Int.quickcheck_generator
  let quickcheck_shrinker = List.quickcheck_shrinker Int.quickcheck_shrinker
end

let qc1 f = T.run_exn (module Single) ~f
let qc2 f = T.run_exn (module Pair) ~f
let qc3 f = T.run_exn (module Triple) ~f
let qcil f = T.run_exn (module Int_list) ~f

let%test_unit "of_list/to_list roundtrip" = qcil @@ fun xs ->
  [%test_eq : int list] (tl (Ftree.of_list xs)) xs

let%test_unit "of_list matches fold+snoc" = qcil @@ fun xs ->
  let v = List.fold xs ~init:Ftree.empty ~f:Ftree.snoc in
  [%test_eq : int list] (tl v) xs

let%test_unit "of_list_rev reverses" = qcil @@ fun xs ->
  [%test_eq : int list] (tl (Ftree.of_list_rev xs)) (List.rev xs)

let%test_unit "singleton" = qcil @@ fun _ ->
  [%test_eq : int list] (tl (Ftree.singleton 7)) [7]

let%test_unit "length matches list length" = qc1 @@ fun t ->
  [%test_eq : int] (Ftree.length t) (List.length (tl t))

let%test_unit "is_empty matches length=0" = qc1 @@ fun t ->
  [%test_eq : bool] (Ftree.is_empty t) (Ftree.length t = 0)

let%test_unit "cons prepends" = qc1 @@ fun t ->
  [%test_eq : int list] (tl (Ftree.cons t 99)) (99 :: tl t)

let%test_unit "snoc appends" = qc1 @@ fun t ->
  [%test_eq : int list] (tl (Ftree.snoc t 99)) (tl t @ [99])

let%test_unit "head matches List.hd" = qc1 @@ fun t ->
  [%test_eq : int option] (Ftree.head t) (List.hd (tl t))

let%test_unit "last matches List.last" = qc1 @@ fun t ->
  [%test_eq : int option] (Ftree.last t) (List.last (tl t))

let%test_unit "tail matches List.tl" = qc1 @@ fun t ->
  [%test_eq : int list option]
    (Option.map (Ftree.tail t) ~f:tl)
    (List.tl (tl t))

let%test_unit "init drops last" = qc1 @@ fun t ->
  let expect = match tl t with
    | [] -> None
    | xs -> Some (List.drop_last_exn xs) in
  [%test_eq : int list option] (Option.map (Ftree.init t) ~f:tl) expect

let%test_unit "front matches head+tail" = qc1 @@ fun t ->
  match Ftree.front t, tl t with
  | None, [] -> ()
  | Some (rest, x), y :: ys ->
    [%test_eq : int] x y;
    [%test_eq : int list] (tl rest) ys
  | _ -> assert false

let%test_unit "rear matches init+last" = qc1 @@ fun t ->
  match Ftree.rear t, List.rev (tl t) with
  | None, [] -> ()
  | Some (rest, x), y :: ys_rev ->
    [%test_eq : int] x y;
    [%test_eq : int list] (tl rest) (List.rev ys_rev)
  | _ -> assert false

let%test_unit "reverse matches List.rev" = qc1 @@ fun t ->
  [%test_eq : int list] (tl (Ftree.reverse t)) (List.rev (tl t))

let%test_unit "reverse is involutive" = qc1 @@ fun t ->
  [%test_eq : int list] (tl (Ftree.reverse (Ftree.reverse t))) (tl t)

let%test_unit "map matches List.map" = qc1 @@ fun t ->
  let f x = x * 3 + 1 in
  [%test_eq : int list] (tl (Ftree.map t ~f)) (List.map (tl t) ~f)

let%test_unit "map_rev matches rev of map" = qc1 @@ fun t ->
  let f x = x - 5 in
  [%test_eq : int list] (tl (Ftree.map_rev t ~f)) (List.rev (List.map (tl t) ~f))

let%test_unit "filter matches List.filter" = qc1 @@ fun t ->
  let f x = x % 2 = 0 in
  [%test_eq : int list] (tl (Ftree.filter t ~f)) (List.filter (tl t) ~f)

let%test_unit "fold matches List.fold" = qc1 @@ fun t ->
  let f acc x = (acc * 31) + x in
  [%test_eq : int] (Ftree.fold t ~init:7 ~f) (List.fold (tl t) ~init:7 ~f)

let%test_unit "fold_right matches List.fold_right" = qc1 @@ fun t ->
  [%test_eq : int list]
    (Ftree.fold_right t ~init:[] ~f:List.cons)
    (tl t)

let%test_unit "iter matches to_list" = qc1 @@ fun t ->
  let acc = ref [] in
  Ftree.iter t ~f:(fun x -> acc := x :: !acc);
  [%test_eq : int list] (List.rev !acc) (tl t)

let%test_unit "iter_rev matches rev of to_list" = qc1 @@ fun t ->
  let acc = ref [] in
  Ftree.iter_rev t ~f:(fun x -> acc := x :: !acc);
  [%test_eq : int list] (List.rev !acc) (List.rev (tl t))

let%test_unit "enum forward and reverse" = qc1 @@ fun t ->
  [%test_eq : int list] (Sequence.to_list (Ftree.enum t)) (tl t);
  [%test_eq : int list] (Sequence.to_list (Ftree.enum ~rev:true t)) (List.rev (tl t))

let%test_unit "append matches list append" = qc2 @@ fun (a, b) ->
  [%test_eq : int list] (tl (Ftree.append a b)) (tl a @ tl b)

let%test_unit "append empty identity (left)" = qc1 @@ fun t ->
  [%test_eq : int list] (tl (Ftree.append Ftree.empty t)) (tl t)

let%test_unit "append empty identity (right)" = qc1 @@ fun t ->
  [%test_eq : int list] (tl (Ftree.append t Ftree.empty)) (tl t)

let%test_unit "append is associative" = qc3 @@ fun (a, b, c) ->
  [%test_eq : int list]
    (tl (Ftree.append (Ftree.append a b) c))
    (tl (Ftree.append a (Ftree.append b c)))

let%test_unit "get matches List.nth" = qc1 @@ fun t ->
  let xs = tl t in
  List.iteri xs ~f:(fun i x -> [%test_eq : int] (Ftree.get_exn t i) x);
  [%test_eq : int option] (Ftree.get t (List.length xs)) None;
  [%test_eq : int option] (Ftree.get t (-1)) None

let%test_unit "lookup_exn equals get_exn" = qc1 @@ fun t ->
  List.iteri (tl t) ~f:(fun i _ ->
      [%test_eq : int]
        (Ftree.lookup_exn t ~f:(fun idx -> i < idx))
        (Ftree.get_exn t i))

let%test_unit "set matches list update" = qc1 @@ fun t ->
  match tl t with
  | [] -> ()
  | xs ->
    let i = List.length xs / 2 in
    [%test_eq : int list]
      (tl (Ftree.set t i 42))
      (List.mapi xs ~f:(fun j x -> if j = i then 42 else x))

let%test_unit "set out of range raises" = qc1 @@ fun t ->
  assert (raises (fun () -> Ftree.set t (Ftree.length t) 0));
  assert (raises (fun () -> Ftree.set t (-1) 0))

let%test_unit "update matches list update" = qc1 @@ fun t ->
  match tl t with
  | [] -> ()
  | xs ->
    let i = List.length xs / 2 in
    let f x = x + 1 in
    [%test_eq : int list]
      (tl (Ftree.update t i ~f))
      (List.mapi xs ~f:(fun j x -> if j = i then f x else x))

let%test_unit "split_at matches List.split_n" = qc1 @@ fun t ->
  match Ftree.length t with
  | 0 -> ()
  | n ->
    let i = n / 2 in
    let l, r = Ftree.split_at_exn t i in
    let l', r' = List.split_n (tl t) i in
    [%test_eq : int list] (tl l) l';
    [%test_eq : int list] (tl r) r'

let%test_unit "split_at out of range is None" = qc1 @@ fun t ->
  [%test_eq : bool] (Option.is_none (Ftree.split_at t (Ftree.length t))) true;
  [%test_eq : bool] (Option.is_none (Ftree.split_at t (-1))) true

let%test_unit "split concatenation law" = qc1 @@ fun t ->
  let k = Quickcheck.random_value Int.quickcheck_generator in
  let l, r = Ftree.split t ~f:(fun n -> n > k) in
  [%test_eq : int list] (tl l @ tl r) (tl t)

let%test_unit "insert matches reference (clamped)" = qc1 @@ fun t ->
  let i = Quickcheck.random_value (Int.gen_incl (-2) 12) in
  [%test_eq : int list] (tl (Ftree.insert t 55 i)) (ref_insert (tl t) 55 i)

let%test_unit "remove matches reference (guarded)" = qc1 @@ fun t ->
  let i = Quickcheck.random_value (Int.gen_incl (-2) 12) in
  [%test_eq : int list] (tl (Ftree.remove t i)) (ref_remove (tl t) i)

let%test_unit "find matches List.find" = qc1 @@ fun t ->
  let f x = x > 0 in
  [%test_eq : int option] (Ftree.find t ~f) (List.find (tl t) ~f)

let%test_unit "findi matches List.findi" = qc1 @@ fun t ->
  let f i x = i > 0 && x % 2 = 0 in
  [%test_eq : (int * int) option] (Ftree.findi t ~f) (List.findi (tl t) ~f)

let%test_unit "index matches reference" = qc1 @@ fun t ->
  let f x = x < 0 in
  [%test_eq : int option] (Ftree.index t ~f) (ref_index (tl t) ~f)

let%test_unit "exists matches List.exists" = qc1 @@ fun t ->
  let target = Quickcheck.random_value Int.quickcheck_generator in
  [%test_eq : bool]
    (Ftree.exists t ~f:(fun x -> x = target))
    (List.exists (tl t) ~f:(fun x -> x = target))

let%test_unit "next matches reference" = qc1 @@ fun t ->
  let f x = x % 3 = 0 in
  [%test_eq : int option] (Ftree.next t ~f) (ref_next (tl t) ~f)

let%test_unit "prev matches reference" = qc1 @@ fun t ->
  let f x = x % 3 = 0 in
  [%test_eq : int option] (Ftree.prev t ~f) (ref_prev (tl t) ~f)

let%test_unit "min_elt matches List.min_elt" = qc1 @@ fun t ->
  [%test_eq : int option]
    (Ftree.min_elt t ~compare:Int.compare)
    (List.min_elt (tl t) ~compare:Int.compare)

let%test_unit "max_elt matches List.max_elt" = qc1 @@ fun t ->
  [%test_eq : int option]
    (Ftree.max_elt t ~compare:Int.compare)
    (List.max_elt (tl t) ~compare:Int.compare)

let%test_unit "remove_if removes first match" = qc1 @@ fun t ->
  let f x = x % 2 = 0 in
  let expect = match ref_index (tl t) ~f with
    | Some j -> ref_remove (tl t) j
    | None -> tl t in
  [%test_eq : int list] (tl (Ftree.remove_if t ~f)) expect

let%test_unit "update_if replaces first match" = qc1 @@ fun t ->
  let f x = x % 2 = 0 in
  let expect = match ref_index (tl t) ~f with
    | Some j -> List.mapi (tl t) ~f:(fun i x -> if i = j then 777 else x)
    | None -> tl t in
  [%test_eq : int list] (tl (Ftree.update_if t 777 ~f)) expect

let%test_unit "equal matches list equal" = qc2 @@ fun (a, b) ->
  [%test_eq : bool]
    (Ftree.equal a b ~equal:Int.equal)
    (List.equal Int.equal (tl a) (tl b))

let%test_unit "equal is reflexive" = qc1 @@ fun t ->
  assert (Ftree.equal t t ~equal:Int.equal)

let%test_unit "compare matches list compare" = qc2 @@ fun (a, b) ->
  let sign x = Int.compare x 0 in
  [%test_eq : int]
    (sign (Ftree.compare a b ~compare:Int.compare))
    (sign (List.compare Int.compare (tl a) (tl b)))

let%test_unit "compare zero iff equal" = qc2 @@ fun (a, b) ->
  if Ftree.equal a b ~equal:Int.equal then
    [%test_eq : int] (Ftree.compare a b ~compare:Int.compare) 0

let%test_unit "sexp round-trip" = qcil @@ fun xs ->
  let t = Ftree.of_list xs in
  let s = Ftree.sexp_of_t Int.sexp_of_t t in
  [%test_eq : int list] (tl (Ftree.t_of_sexp Int.t_of_sexp s)) xs

let%test_unit "empty behaviors" =
  let e : int Ftree.t = Ftree.empty in
  assert (Ftree.is_empty e);
  assert (Ftree.length e = 0);
  assert (Option.is_none (Ftree.head e));
  assert (Option.is_none (Ftree.last e));
  assert (Option.is_none (Ftree.front e));
  assert (Option.is_none (Ftree.rear e));
  assert (Option.is_none (Ftree.tail e));
  assert (Option.is_none (Ftree.init e));
  assert (raises (fun () -> Ftree.head_exn e));
  assert (raises (fun () -> Ftree.last_exn e));
  assert (raises (fun () -> Ftree.front_exn e));
  assert (raises (fun () -> Ftree.rear_exn e));
  assert (raises (fun () -> Ftree.get_exn e 0))

type op =
  | Cons of int
  | Snoc of int
  | Insert of int * int
  | Remove of int
  | Set of int * int
  | Reverse
  | Filter_even
  | Append of int list
[@@deriving sexp_of]

let apply_model m = function
  | Cons x -> x :: m
  | Snoc x -> m @ [x]
  | Insert (i, x) -> ref_insert m x i
  | Remove i -> ref_remove m i
  | Set (i, x) ->
    if i >= 0 && i < List.length m
    then List.mapi m ~f:(fun j y -> if j = i then x else y)
    else m
  | Reverse -> List.rev m
  | Filter_even -> List.filter m ~f:(fun x -> x % 2 = 0)
  | Append xs -> m @ xs

let apply_ft t = function
  | Cons x -> Ftree.cons t x
  | Snoc x -> Ftree.snoc t x
  | Insert (i, x) -> Ftree.insert t x i
  | Remove i -> Ftree.remove t i
  | Set (i, x) -> if i >= 0 && i < Ftree.length t then Ftree.set t i x else t
  | Reverse -> Ftree.reverse t
  | Filter_even -> Ftree.filter t ~f:(fun x -> x % 2 = 0)
  | Append xs -> Ftree.append t (Ftree.of_list xs)

let gen_val = Int.quickcheck_generator
let gen_idx = Int.gen_incl (-3) 10

let gen_op = G.weighted_union [
    3., G.map gen_val ~f:(fun x -> Cons x);
    3., G.map gen_val ~f:(fun x -> Snoc x);
    2., G.map (G.tuple2 gen_idx gen_val) ~f:(fun (i, x) -> Insert (i, x));
    2., G.map gen_idx ~f:(fun i -> Remove i);
    2., G.map (G.tuple2 gen_idx gen_val) ~f:(fun (i, x) -> Set (i, x));
    1., G.return Reverse;
    1., G.return Filter_even;
    2., G.map (G.list gen_val) ~f:(fun xs -> Append xs);
  ]

module Ops = struct
  type t = op list [@@deriving sexp_of]
  let quickcheck_generator = List.quickcheck_generator gen_op
  let quickcheck_shrinker = List.quickcheck_shrinker (S.empty ())
end

let%test_unit "state-machine test" =
  T.run_exn (module Ops) ~f:(fun ops ->
      let rec loop model t = function
        | [] -> ()
        | op :: rest ->
          let expect = apply_model model op in
          let t' = apply_ft t op in
          let result = tl t' in
          if not (List.equal Int.equal result expect) then
            raise_s [%sexp "state mismatch", {
                op     : op;
                model  : int list;
                result : int list;
                expect : int list;
              }];
          loop expect t' rest in
      loop [] Ftree.empty ops)
