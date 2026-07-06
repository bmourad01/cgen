open Core

module Q = Quickcheck
module G = Q.Generator
module S = Q.Shrinker
module T = Base_quickcheck.Test
module Seq = Sequence

module type Key = sig
  type t
  include Cgen_containers.Small_map_intf.Key with type t := t
  include Q.S with type t := t
end

let value_gen = Int.quickcheck_generator
let value_shrink = Int.quickcheck_shrinker

module Make(K : Key) = struct
  module Ref = Map.Make(K)
  module Sm = Cgen_containers.Small_map.Make(K)

  type upd = Inc | Dec | Const of int [@@deriving quickcheck, sexp_of]

  type op =
    | Set    of K.t * int
    | Add    of K.t * int
    | Remove of K.t
    | Update of K.t * upd
  [@@deriving quickcheck, sexp_of]

  let key_gen = K.quickcheck_generator
  let key_shrink = K.quickcheck_shrinker

  let kv_gen = G.tuple2 key_gen value_gen
  let kv_shrink = S.tuple2 key_shrink value_shrink

  (* Deliberately generate lots of keys so the trees grow past the leaf cases
     and exercise the AVL balancing and removal paths. *)
  let kv_list_gen =
    let open G in
    size >>= fun sz -> list_with_length (sz * 5) kv_gen

  let kv_list_shrink = List.quickcheck_shrinker kv_shrink

  let of_alist_ref l =
    List.fold l ~init:Ref.empty ~f:(fun acc (k, v) -> Map.set acc ~key:k ~data:v)

  let of_alist_sm l =
    List.fold l ~init:Sm.empty ~f:(fun acc (k, v) -> Sm.set acc ~key:k ~data:v)

  let op_gen = quickcheck_generator_op
  let op_shrink = quickcheck_shrinker_op
  let ops_gen = G.list op_gen
  let ops_shrink = List.quickcheck_shrinker op_shrink

  let apply_upd = function
    | Inc -> succ, Fn.const 1
    | Dec -> pred, Fn.const (-1)
    | Const k -> Fn.const k, Fn.const k

  let apply_ref t = function
    | Set (k, v) -> Map.set t ~key:k ~data:v
    | Add (k, v) ->
      begin match Map.add t ~key:k ~data:v with
        | `Ok t' -> t' | `Duplicate -> t
      end
    | Remove k -> Map.remove t k
    | Update (k, u) ->
      let has, nil = apply_upd u in
      Map.update t k ~f:(function None -> nil () | Some v -> has v)

  let apply_sm t = function
    | Set (k, v) -> Sm.set t ~key:k ~data:v
    | Add (k, v) ->
      begin match Sm.add t ~key:k ~data:v with
        | `Ok t' -> t' | `Duplicate -> t
      end
    | Remove k -> Sm.remove t k
    | Update (k, u) ->
      let has, nil = apply_upd u in
      Sm.update_with t k ~has ~nil

  let to_alist_ref t = Map.to_alist t
  let to_alist_sm t = Sm.to_list t
  let eq2 (k1, v1) (k2, v2) = K.compare k1 k2 = 0 && v1 = v2
  let cmp2 (k1, _) (k2, _) = K.compare k1 k2

  module Kv2 = struct
    type t = K.t * int * int [@@deriving sexp_of]
    let quickcheck_generator = G.tuple3 key_gen value_gen value_gen
    let quickcheck_shrinker = S.tuple3 key_shrink value_shrink value_shrink
  end

  module Ops_key = struct
    type t = op list * K.t [@@deriving sexp_of]
    let quickcheck_generator = G.tuple2 ops_gen key_gen
    let quickcheck_shrinker = S.tuple2 ops_shrink key_shrink
  end

  module Kv_list = struct
    type t = (K.t * int) list [@@deriving sexp_of]
    let quickcheck_generator = kv_list_gen
    let quickcheck_shrinker = kv_list_shrink
  end

  module Kv_list_ops = struct
    type t = (K.t * int) list * op list [@@deriving sexp_of]
    let quickcheck_generator = G.tuple2 kv_list_gen ops_gen
    let quickcheck_shrinker = S.tuple2 kv_list_shrink ops_shrink
  end

  module Two_kv_lists = struct
    type t = (K.t * int) list * (K.t * int) list [@@deriving sexp_of]
    let quickcheck_generator = G.tuple2 kv_list_gen kv_list_gen
    let quickcheck_shrinker = S.tuple2 kv_list_shrink kv_list_shrink
  end

  let qckv2 f = T.run_exn (module Kv2) ~f
  let qcok f = T.run_exn (module Ops_key) ~f
  let qckvl f = T.run_exn (module Kv_list) ~f
  let qckvlo f = T.run_exn (module Kv_list_ops) ~f
  let qc2l f = T.run_exn (module Two_kv_lists) ~f

  let%test_unit "set overwrites" = qckv2 @@ fun (k, v1, v2) ->
    let t = of_alist_sm [k, v1; k, v2] in
    [%test_eq : int option] (Sm.find t k) (Some v2)

  let%test_unit "add detects duplicates" = qckv2 @@ fun (k, v1, v2) ->
    let t = Sm.singleton k v1 in
    match Sm.add t ~key:k ~data:v2 with
    | `Duplicate -> () | `Ok _ -> assert false

  let%test_unit "remove is idempotent" = qcok @@ fun (ops, k) ->
    let t = List.fold ops ~init:Sm.empty ~f:apply_sm in
    let t1 = Sm.remove t k in
    let t2 = Sm.remove t1 k in
    [%test_eq : (K.t * int) list] (to_alist_sm t1) (to_alist_sm t2)

  let%test_unit "initialized iteration equivalence" = qckvl @@ fun kvs ->
    [%test_eq : (K.t * int) list]
      (to_alist_sm (of_alist_sm kvs)) (to_alist_ref (of_alist_ref kvs))

  let%test_unit "to_sequence equals to_list" = qckvl @@ fun kvs ->
    let t = of_alist_sm kvs in
    [%test_eq : (K.t * int) list] (Seq.to_list (Sm.to_sequence t)) (Sm.to_list t)

  let%test_unit "to_sequence_rev is reverse of to_list" = qckvl @@ fun kvs ->
    let t = of_alist_sm kvs in
    [%test_eq : (K.t * int) list]
      (Seq.to_list (Sm.to_sequence_rev t)) (List.rev (Sm.to_list t))

  let%test_unit "behaves like Map under operations" = qckvlo @@ fun (kvs, ops) ->
    let rec loop r c = function
      | [] -> ()
      | op :: rest ->
        let r' = apply_ref r op and c' = apply_sm c op in
        let expect = to_alist_ref r' and result = to_alist_sm c' in
        if not (List.equal eq2 expect result) then
          raise_s [%sexp "state mismatch",
                         { op : op; result : (K.t * int) list;
                           expect : (K.t * int) list }];
        loop r' c' rest in
    loop (of_alist_ref kvs) (of_alist_sm kvs) ops

  (* A non-commutative combine, so a wrong left/right in any merge_XX case is
     caught (merge passes the left map's value first). *)
  let combine ~key:_ a b = (a * 31) + b

  let%test_unit "merge behaves like Map.merge_skewed" = qc2l @@ fun (l1, l2) ->
    let sm = Sm.merge (of_alist_sm l1) (of_alist_sm l2) ~f:combine in
    let rf =
      Map.merge_skewed (of_alist_ref l1) (of_alist_ref l2)
        ~combine:(fun ~key a b -> combine ~key a b) in
    [%test_eq : (K.t * int) list] (to_alist_sm sm) (to_alist_ref rf)

  let%test_unit "length and fold count keys" = qckvl @@ fun kvs ->
    let t = of_alist_sm kvs in
    let unique = List.dedup_and_sort kvs ~compare:cmp2 in
    [%test_eq : int] (Sm.length t) (List.length unique);
    [%test_eq : int] (Sm.fold t ~init:0 ~f:(fun acc _ -> acc + 1)) (List.length unique)

  let%test_unit "foldi accumulates key-value pairs in order" = qckvl @@ fun kvs ->
    let t = of_alist_sm kvs in
    let got =
      Sm.foldi t ~init:[] ~f:(fun ~key ~data acc -> (key, data) :: acc)
      |> List.rev in
    [%test_eq : (K.t * int) list] got (Sm.to_list t)

  let%test_unit "keys and data agree with to_list" = qckvl @@ fun kvs ->
    let t = of_alist_sm kvs in
    let kvl = Sm.to_list t in
    [%test_eq : K.t list] (Sm.keys t) (List.map kvl ~f:fst);
    [%test_eq : int list] (Sm.data t) (List.map kvl ~f:snd)

  let%test_unit "mem and find are congruent" = qckvl @@ fun kvs ->
    let t = of_alist_sm kvs in
    List.iter (Sm.to_list t) ~f:(fun (k, v) ->
        assert (Sm.mem t k);
        [%test_eq : int option] (Sm.find t k) (Some v))

  let%test_unit "sexp round-trips" = qckvl @@ fun kvs ->
    let t = of_alist_sm kvs in
    let s = [%sexp_of : int Sm.t] t in
    [%test_eq : (K.t * int) list] (to_alist_sm ([%of_sexp : int Sm.t] s)) (to_alist_sm t)
end

module Int_key = struct
  module T = struct
    type t = int [@@deriving compare, equal, quickcheck, sexp]
  end
  include T
end

(* A key with many collisions in a small range, to stress the balancing. *)
module Small_range_key = struct
  module T = struct
    type t = int [@@deriving compare, equal, sexp]
  end
  include T
  let quickcheck_generator = Int.gen_incl 0 12
  let quickcheck_shrinker = Int.quickcheck_shrinker
  let quickcheck_observer = Int.quickcheck_observer
end

module Pair_key = struct
  module T = struct
    type t = int * string [@@deriving compare, equal, quickcheck, sexp]
  end
  include T
end

module _ = Make(Int_key)
module _ = Make(Small_range_key)
module _ = Make(Pair_key)
