open Core

module Q = Quickcheck
module G = Q.Generator
module S = Q.Shrinker
module O = Q.Observer
module T = Base_quickcheck.Test
module Seq = Sequence

module type Key = sig
  type t
  include Cgen_containers.Champ_intf.Key with type t := t
  include Sexpable.S with type t := t
  include Q.S with type t := t
end

let value_gen = Int.quickcheck_generator
let value_shrink = Int.quickcheck_shrinker

module Make(K : Key) = struct
  module Ref = Map.Make(K)
  module Champ = Cgen_containers.Champ.Make(K)

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

  let kv_list_gen =
    let open G in
    size >>= fun sz ->
    list_with_length (sz * 5) kv_gen

  let kv_list_shrink = List.quickcheck_shrinker kv_shrink

  let of_alist_ref l =
    List.fold l ~init:Ref.empty ~f:(fun acc (k, v) ->
        Map.set acc ~key:k ~data:v)

  let of_alist_champ = Champ.of_alist_overwrite

  let op_gen = quickcheck_generator_op
  let op_shrink = quickcheck_shrinker_op

  let ops_gen = G.list op_gen
  let ops_shrink = List.quickcheck_shrinker op_shrink

  let update_with_ref t k ~has ~nil =
    Map.update t k ~f:(function
        | None -> nil ()
        | Some v -> has v)

  let apply_upd = function
    | Inc -> succ, Fn.const 1
    | Dec -> pred, Fn.const (-1)
    | Const k -> Fn.const k, Fn.const k

  let apply_ref t = function
    | Set (k, v) -> Map.set t ~key:k ~data:v
    | Add (k, v) ->
      begin match Map.add t ~key:k ~data:v with
        | `Ok t' -> t'
        | `Duplicate -> t
      end
    | Remove k -> Map.remove t k
    | Update (k, u) ->
      let has, nil = apply_upd u in
      update_with_ref t k ~has ~nil

  let apply_champ t = function
    | Set (k, v) -> Champ.set t ~key:k ~data:v
    | Add (k, v) ->
      begin match Champ.add t ~key:k ~data:v with
        | `Ok t' -> t'
        | `Duplicate -> t
      end
    | Remove k -> Champ.remove t k
    | Update (k, u) ->
      let has, nil = apply_upd u in
      Champ.update_with t k ~has ~nil

  let sort l = List.sort l ~compare:(fun (k1, _) (k2, _) -> K.compare k1 k2)

  let normalize l = sort l |> List.fold_right ~init:[]
      ~f:(fun (k, v) acc -> match acc with
          | (k', _) :: _ when K.compare k k' = 0 -> acc
          | _ -> (k, v) :: acc)

  let to_alist_ref t = Map.to_alist t
  let to_sequence_ref t = Map.to_sequence t
  let to_alist_champ t = sort (Champ.to_alist t)

  let to_sequence_champ t =
    Champ.to_sequence t |>
    Sequence.to_list |>
    sort |>
    Sequence.of_list

  let eq2 (k1, v1) (k2, v2) = K.compare k1 k2 = 0 && v1 = v2

  module Key_v1 = struct
    type t = K.t * int [@@deriving sexp_of]
    let quickcheck_generator = G.tuple2 key_gen value_gen
    let quickcheck_shrinker = S.tuple2 key_shrink value_shrink
  end

  module Key_v2 = struct
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

  let qckv1 f = T.run_exn (module Key_v1) ~f
  let qckv2 f = T.run_exn (module Key_v2) ~f
  let qcok f = T.run_exn (module Ops_key) ~f
  let qckvl f = T.run_exn (module Kv_list) ~f
  let qckvlo f = T.run_exn (module Kv_list_ops) ~f

  let%test_unit "set overwrites" = qckv2 @@ fun (k, v1, v2) ->
    let t = Champ.of_alist_overwrite [k, v1; k, v2] in
    [%test_eq : int option] (Champ.find t k) (Some v2)

  let%test_unit "add detects duplicates" = qckv1 @@ fun (k, v) ->
    let t = Champ.singleton k v in
    match Champ.add t ~key:k ~data:v with
    | `Duplicate -> ()
    | `Ok _ -> assert false

  let%test_unit "remove is idempotent" = qcok @@ fun (ops, k) ->
    let t = List.fold ops ~init:Champ.empty ~f:apply_champ in
    let t1 = Champ.remove t k in
    let t2 = Champ.remove t1 k in
    [%test_eq : (K.t * int) list] (to_alist_champ t1) (to_alist_champ t2)

  let%test_unit "initialized champ iteration equivalence" = qckvl @@ fun kvs ->
    let c = of_alist_champ kvs in
    let r = of_alist_ref kvs in
    [%test_eq : (K.t * int) list] (to_alist_champ c) (to_alist_ref r)

  let%test_unit "initialized champ iteration equivalence (seq)" = qckvl @@ fun kvs ->
    let c = of_alist_champ kvs in
    let r = of_alist_ref kvs in
    [%test_eq : (K.t * int) Sequence.t] (to_sequence_champ c) (to_sequence_ref r)

  let%test_unit "champ behaves like Map under operations" = qckvlo @@ fun (kvs, ops) ->
    let rec loop r c = function
      | [] -> ()
      | op :: rest ->
        let r' = apply_ref r op in
        let c' = apply_champ c op in
        let expect = to_alist_ref r' in
        let result = to_alist_champ c' in
        if not (List.equal eq2 expect result) then
          raise_s [%sexp "state mismatch", {
              op     : op;
              r      : int Ref.t;
              result : (K.t * int) list;
              expect : (K.t * int) list;
            }];
        loop r' c' rest in
    loop (of_alist_ref kvs) (of_alist_champ kvs) ops

  let cmp2 (k1, _) (k2, _) = K.compare k1 k2

  let%test_unit "fold counts keys" = qckvl @@ fun kvs ->
    let t = of_alist_champ kvs in
    let count = Champ.fold t ~init:0 ~f:(fun acc _ -> acc + 1) in
    let unique = List.dedup_and_sort kvs ~compare:cmp2 in
    [%test_eq: int] count (List.length unique)

  let%test_unit "length counts keys" = qckvl @@ fun kvs ->
    let t = of_alist_champ kvs in
    let count = Champ.length t in
    let unique = List.dedup_and_sort kvs ~compare:cmp2 in
    [%test_eq: int] count (List.length unique)

  let%test_unit "update_with ~= set when has ignores old value" = qckv2 @@ fun (k, v1, v2) ->
    let t0 = Champ.singleton k v1 in
    let t1 = Champ.update_with t0 k
        ~has:(fun _ -> v2)
        ~nil:(fun () -> v2) in
    [%test_eq : int option] (Champ.find t1 k) (Some v2)

  let%test_unit "update_with inserts when key absent" = qckv1 @@ fun (k, v) ->
    let t = Champ.update_with Champ.empty k
        ~has:(fun _ -> assert false)
        ~nil:(fun () -> v) in
    [%test_eq : int option] (Champ.find t k) (Some v)

  let%test_unit "update_with inserts when key present" = qckv2 @@ fun (k, v1, v2) ->
    let t0 = Champ.singleton k v1 in
    let t1 = Champ.update_with t0 k
        ~has:(fun _ -> v2)
        ~nil:(fun () -> assert false) in
    [%test_eq : int option] (Champ.find t1 k) (Some v2)

  let%test_unit "mem and find are congruent" = qckvl @@ fun kvs ->
    let kvs' = normalize kvs in
    let t = of_alist_champ kvs in
    List.iter kvs' ~f:(fun (k, v) ->
        assert (Champ.mem t k);
        [%test_eq : int option] (Champ.find t k) (Some v))
end

module Key = struct
  module T = struct
    type t = int * string [@@deriving bin_io, compare, equal, hash, quickcheck, sexp]
  end
  include T
  include Comparator.Make(T)
end

module Flood_key_const = struct
  module T = struct
    type t = int [@@deriving bin_io, equal, compare, quickcheck, sexp]
    let hash _ = 0
    let hash_fold_t state t = hash_fold_int state (hash t)
  end
  include T
  include Comparator.Make(T)
end

module Flood_key_alternating = struct
  module T = struct
    type t = int [@@deriving bin_io, equal, compare, quickcheck, sexp]
    let hash k = k land 1
    let hash_fold_t state t = hash_fold_int state (hash t)
  end
  include T
  include Comparator.Make(T)
end

module _ = Make(Key)
module _ = Make(Flood_key_const)
module _ = Make(Flood_key_alternating)
