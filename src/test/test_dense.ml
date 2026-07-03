open Core
open Cgen_containers

module T = Base_quickcheck.Test
module G = Base_quickcheck.Generator
module O = Base_quickcheck.Observer
module S = Base_quickcheck.Shrinker

module Key = struct
  type t = int [@@deriving equal]
  let empty_sentinel = -1
  let to_int = Fn.id
  let pp = Int.pp
end

module M = Dense.Make_map(Key)
module DS = Dense.Make_set(Key)

let gen_key = G.int_inclusive 0 200

type mop =
  | Set of int * int
  | Update of int
  | Find_or_add of int * int
  | Change_remove of int
  | Remove of int
[@@deriving sexp]

type sop = Add of int | Sremove of int [@@deriving sexp]

let gen_mop =
  let open G.Let_syntax in
  match%bind G.int_inclusive 0 4 with
  | 0 ->
    let%bind k = gen_key in
    let%map v = G.small_positive_or_zero_int in
    Set (k, v)
  | 1 ->
    let%map k = gen_key in
    Update k
  | 2 ->
    let%bind k = gen_key in
    let%map v = G.small_positive_or_zero_int in
    Find_or_add (k, v)
  | 3 ->
    let%map k = gen_key in
    Change_remove k
  | _ ->
    let%map k = gen_key in
    Remove k

let gen_sop =
  let open G.Let_syntax in
  match%bind G.int_inclusive 0 1 with
  | 0 ->
    let%map k = gen_key in
    Add k
  | _ ->
    let%map k = gen_key in
    Sremove k

module Mops = struct
  type t = mop list [@@deriving sexp]
  let quickcheck_generator = G.list gen_mop
  let quickcheck_observer : t O.t = O.opaque
  let quickcheck_shrinker : t S.t = S.list S.atomic
end

module Sops = struct
  type t = sop list [@@deriving sexp]
  let quickcheck_generator = G.list gen_sop
  let quickcheck_observer : t O.t = O.opaque
  let quickcheck_shrinker : t S.t = S.list S.atomic
end

let incr = Option.value_map ~default:0 ~f:succ

let apply_ref r = function
  | Set (k, v) -> Map.set r ~key:k ~data:v
  | Update k -> Map.update r k ~f:incr
  | Find_or_add (k, v) when Map.mem r k -> r
  | Find_or_add (k, v) -> Map.set r ~key:k ~data:v
  | Change_remove k | Remove k -> Map.remove r k

let apply_dense m = function
  | Set (k, v) -> M.set m ~key:k ~data:v
  | Update k -> M.update m k ~f:incr
  | Find_or_add (k, v) ->
    ignore (M.find_or_add m k ~default:(fun () -> v) : int)
  | Change_remove k -> M.change m k ~f:(fun _ -> None)
  | Remove k -> M.remove m k

let%test_unit "map matches Int.Map under a random op sequence" =
  T.run_exn (module Mops) ~f:(fun ops ->
      let m = M.create () in
      let r = List.fold ops ~init:Int.Map.empty ~f:(fun r op ->
          let r = apply_ref r op in
          apply_dense m op;
          [%test_result : int] (M.length m) ~expect:(Map.length r);
          r) in
      [%test_result : (int * int) list]
        (M.to_alist m |> List.sort ~compare:[%compare : int * int])
        ~expect:(Map.to_alist r);
      for k = 0 to 200 do
        [%test_result : int option] (M.find m k) ~expect:(Map.find r k)
      done)

let%test_unit "set matches Int.Set under a random op sequence" =
  T.run_exn (module Sops) ~f:(fun ops ->
      let s = DS.create () in
      let r = List.fold ops ~init:Int.Set.empty ~f:(fun r op ->
          let r = match op with
            | Add k ->
              let fresh = not (Set.mem r k) in
              [%test_result : bool] (DS.strict_add s k) ~expect:fresh;
              Set.add r k
            | Sremove k ->
              DS.remove s k;
              Set.remove r k in
          [%test_result : int] (DS.length s) ~expect:(Set.length r);
          r) in
      [%test_result : int list]
        (DS.to_list s |> List.sort ~compare:Int.compare)
        ~expect:(Set.to_list r);
      for k = 0 to 200 do
        [%test_result : bool] (DS.mem s k) ~expect:(Set.mem r k)
      done)
