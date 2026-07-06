open Core

module Q = Quickcheck
module G = Q.Generator
module S = Q.Shrinker
module T = Base_quickcheck.Test

module H = Cgen_containers.Hdict.Make(struct
    type t = string
    let to_string = Fn.id
  end)

(* A pool of int-valued keys, enough to grow the tree past the leaf cases and
   exercise the AVL balancing and removal over the GADT.

   The reference model is an `Int.Map` keyed by each key's index in this array.
*)
let n = 24
let keys : int H.Key.t array =
  Array.init n ~f:(fun i -> H.Key.create ~name:(sprintf "k%d" i) [%sexp_of: int])

(* A non-commutative combine, so a wrong left/right in merge/update is caught. *)
let combine a b = (a * 31) + b

type op =
  | Set of int * int
  | Remove of int
  | Update of int * int
[@@deriving sexp_of]

let idx_gen = Int.gen_incl 0 (n - 1)
let val_gen = Int.quickcheck_generator

let op_gen =
  let open G in
  union
    [ map (tuple2 idx_gen val_gen) ~f:(fun (i, v) -> Set (i, v))
    ; map idx_gen ~f:(fun i -> Remove i)
    ; map (tuple2 idx_gen val_gen) ~f:(fun (i, v) -> Update (i, v))
    ]

let ops_gen = G.list op_gen

let apply_h h = function
  | Set (i, v) -> H.set keys.(i) v h
  | Remove i -> H.remove keys.(i) h
  | Update (i, v) -> H.update combine keys.(i) v h

let apply_r r = function
  | Set (i, v) -> Map.set r ~key:i ~data:v
  | Remove i -> Map.remove r i
  | Update (i, v) ->
    Map.update r i ~f:(function None -> v | Some old -> combine old v)

let build_h ops = List.fold ops ~init:H.empty ~f:apply_h
let build_r ops = List.fold ops ~init:Int.Map.empty ~f:apply_r

let check_equiv h r =
  [%test_eq : int] (H.length h) (Map.length r);
  Array.iteri keys ~f:(fun i k ->
      [%test_eq : int option] (H.find k h) (Map.find r i);
      [%test_eq : bool] (H.mem k h) (Map.mem r i))

module Ops = struct
  type t = op list [@@deriving sexp_of]
  let quickcheck_generator = ops_gen
  let quickcheck_shrinker = List.quickcheck_shrinker (S.empty ())
end

module Two_ops = struct
  type t = op list * op list [@@deriving sexp_of]
  let quickcheck_generator = G.tuple2 ops_gen ops_gen
  let quickcheck_shrinker =
    S.tuple2 (List.quickcheck_shrinker (S.empty ())) (List.quickcheck_shrinker (S.empty ()))
end

let qc f = T.run_exn (module Ops) ~f
let qc2 f = T.run_exn (module Two_ops) ~f

let%test_unit "behaves like Map under operations" = qc @@ fun ops ->
  check_equiv (build_h ops) (build_r ops)

let%test_unit "remove is idempotent" = qc @@ fun ops ->
  let h = build_h ops in
  Array.iter keys ~f:(fun k ->
      let h1 = H.remove k h in
      let h2 = H.remove k h1 in
      [%test_eq : int option array]
        (Array.map keys ~f:(fun j -> H.find j h1))
        (Array.map keys ~f:(fun j -> H.find j h2)))

let%test_unit "merge is union, right value wins on collision" = qc2 @@ fun (o1, o2) ->
  let hm = H.merge { merge = (fun _ _ b -> b) } (build_h o1) (build_h o2) in
  let rm =
    Map.merge_skewed (build_r o1) (build_r o2) ~combine:(fun ~key:_ _ b -> b) in
  check_equiv hm rm

let%test_unit "merge is union, left value wins on collision" = qc2 @@ fun (o1, o2) ->
  let hm = H.merge { merge = (fun _ a _ -> a) } (build_h o1) (build_h o2) in
  let rm =
    Map.merge_skewed (build_r o1) (build_r o2) ~combine:(fun ~key:_ a _ -> a) in
  check_equiv hm rm

let%test_unit "merge over rank-1 leaves matches the reference" =
  let small_idx = Int.gen_incl 0 3 in
  let small_op =
    let open G in
    map (tuple2 small_idx val_gen) ~f:(fun (i, v) -> Set (i, v)) in
  let module Small = struct
    type t = op list * op list [@@deriving sexp_of]
    let quickcheck_generator = G.tuple2 (G.list small_op) (G.list small_op)
    let quickcheck_shrinker = S.tuple2 (S.empty ()) (S.empty ())
  end in
  T.run_exn (module Small) ~f:(fun (o1, o2) ->
      let x = build_h o1 and y = build_h o2 in
      assert (H.Internal.is_rank1 x || H.is_empty x);
      assert (H.Internal.is_rank1 y || H.is_empty y);
      let rx = build_r o1 and ry = build_r o2 in
      let hl = H.merge { merge = (fun _ a _ -> a) } x y in
      check_equiv hl (Map.merge_skewed rx ry ~combine:(fun ~key:_ a _ -> a));
      let hr = H.merge { merge = (fun _ _ b -> b) } x y in
      check_equiv hr (Map.merge_skewed rx ry ~combine:(fun ~key:_ _ b -> b)))

let%test_unit "singleton / is_empty / length" = qc @@ fun ops ->
  let h = build_h ops in
  [%test_eq : bool] (H.is_empty h) (H.length h = 0);
  [%test_eq : bool] (H.is_empty (H.singleton keys.(0) 1)) false;
  [%test_eq : int] (H.length (H.singleton keys.(0) 1)) 1

let%test_unit "foreach visits every binding once, in uid order" = qc @@ fun ops ->
  let h = build_h ops and r = build_r ops in
  let uids =
    H.foreach h ~init:[] { visit = fun k _ acc -> H.Key.uid k :: acc }
    |> List.rev in
  [%test_eq : int] (List.length uids) (Map.length r);
  [%test_result : bool] ~expect:true (List.is_sorted uids ~compare:Int.compare)

let%test_unit "heterogeneous keys round-trip" =
  let ki = H.Key.create ~name:"i" [%sexp_of : int] in
  let kb = H.Key.create ~name:"b" [%sexp_of : bool] in
  let ks = H.Key.create ~name:"s" [%sexp_of : string] in
  let h = H.set ki 42 (H.set kb true (H.set ks "hi" H.empty)) in
  [%test_eq : int option] (H.find ki h) (Some 42);
  [%test_eq : bool option] (H.find kb h) (Some true);
  [%test_eq : string option] (H.find ks h) (Some "hi");
  let h = H.remove kb h in
  [%test_eq : bool option] (H.find kb h) None;
  [%test_eq : int option] (H.find ki h) (Some 42);
  [%test_eq : string option] (H.find ks h) (Some "hi")

let%test_unit "get raises when absent" =
  match H.get keys.(0) H.empty with
  | exception H.Not_found -> ()
  | _ -> assert false

let%test_unit "add detects duplicates" =
  let h = H.set keys.(0) 5 H.empty in
  match H.add keys.(0) 7 h with
  | `Duplicate -> ()
  | `Ok _ -> assert false

let%test_unit "change inserts, updates, and removes" =
  let bump = function None -> Some 1 | Some x -> Some (x + 1) in
  let h = H.change keys.(0) H.empty ~f:bump in
  [%test_eq : int option] (H.find keys.(0) h) (Some 1);
  let h = H.change keys.(0) h ~f:bump in
  [%test_eq : int option] (H.find keys.(0) h) (Some 2);
  let h = H.change keys.(0) h ~f:(fun _ -> None) in
  [%test_eq : int option] (H.find keys.(0) h) None
