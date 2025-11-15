open Core
open Regular.Std

module Make_helpers(K : Patricia_tree_intf.Key) = struct
  open K

  let () = assert (size > 0)

  let _ = pp (* silence warning *)

  let is_neg x = compare x zero < 0 [@@inline]
  let zero_bit x ~bit = equal (x land bit) zero [@@inline]
  let highest_bit x = one lsl Int.(pred size - K.clz x) [@@inline]
  let branching_bit a b = highest_bit (a lxor b) [@@inline]
  let mask x ~bit = x land (neg (bit lsl 1)) [@@inline]
  let match_prefix x ~prefix ~bit = equal (mask x ~bit) prefix [@@inline]
  let equal_prefix p1 b1 p2 b2 = equal b1 b2 && equal p1 p2 [@@inline]

  let higher b1 b2 = match is_neg b1, is_neg b2 with
    | false, false -> compare b1 b2 > 0
    | _, true -> false
    | true, false -> true
  [@@inline]

  let includes_prefix p1 b1 p2 b2 =
    higher b1 b2 && match_prefix p2 ~prefix:p1 ~bit:b1
  [@@inline]

  let compare_prefix p1 b1 p2 b2 =
    let c = compare b1 b2 in
    if c = 0 then compare p1 p2 else c

  type order = NA | LB | RB

  let order x ~prefix ~bit =
    if match_prefix x ~prefix ~bit then
      if zero_bit x ~bit then LB else RB
    else NA
  [@@inline]

  type order2 = EQ | LIL | LIR | RIL | RIR | DJ

  let order2 p1 b1 p2 b2 =
    if equal_prefix p1 b1 p2 b2 then EQ
    else if includes_prefix p1 b1 p2 b2 then
      if zero_bit p2 ~bit:b1 then LIL else LIR
    else if includes_prefix p2 b2 p1 b1 then
      if zero_bit p1 ~bit:b2 then RIL else RIR
    else DJ
  [@@inline]
end

(* Implementation of a PATRICIA tree, adapted from BAP:

   https://github.com/BinaryAnalysisPlatform/bap/blob/517db3d15ee98e914cd970ab4a9bf4d17b65ee35/lib/knowledge/bap_knowledge.ml#L82

   Except without the compressed prefix and branching bit optimization.
*)
module Make(K : Patricia_tree_intf.Key) = struct
  type key = K.t

  open Make_helpers(K)

  type +'a t =
    | Bin of key * key * 'a t * 'a t
    | Tip of key * 'a
    | Nil

  type 'a or_duplicate = [
    | `Ok of 'a t
    | `Duplicate
  ]

  let empty = Nil

  let is_empty = function
    | Bin _ | Tip _ -> false
    | Nil -> true
  [@@inline]

  exception Not_found
  exception Duplicate

  let rec find_exn t k = match t with
    | Nil -> raise Not_found
    | Tip (k', v) when K.equal k k' -> v
    | Tip _ -> raise Not_found
    | Bin (p, b, l, r) -> match order k ~prefix:p ~bit:b with
      | NA -> raise Not_found
      | LB -> find_exn l k
      | RB -> find_exn r k

  let find t k = try Some (find_exn t k) with
    | Not_found -> None

  let mem t k = try ignore (find_exn t k); true with
    | Not_found -> false

  let of_key p b l r = match l, r with
    | Nil, o | o, Nil -> o
    | _ -> Bin (p, b, l, r)

  let join t1 p1 t2 p2 =
    let bit = branching_bit p1 p2 in
    let m = mask p1 ~bit in
    if zero_bit p1 ~bit
    then of_key m bit t1 t2
    else of_key m bit t2 t1

  let singleton k v = Tip (k, v)

  let rec update_with t k ~has ~nil = match t with
    | Nil -> Tip (k, nil ())
    | Tip (k', v') when K.equal k k' -> Tip (k, has v')
    | Tip (k', _) -> join t k' (Tip (k, nil ())) k
    | Bin (p, b, l, r) -> match order k ~prefix:p ~bit:b with
      | NA -> join (Tip (k, nil ())) k t p
      | LB -> Bin (p, b, update_with l k ~has ~nil, r)
      | RB -> Bin (p, b, l, update_with r k ~has ~nil)
  [@@specialise]

  let rec update t k ~f = match t with
    | Nil -> Tip (k, f None)
    | Tip (k', v') when K.equal k k' -> Tip (k, f (Some v'))
    | Tip (k', _) -> join t k' (Tip (k, f None)) k
    | Bin (p, b, l, r) -> match order k ~prefix:p ~bit:b with
      | NA -> join (Tip (k, f None)) k t p
      | LB -> Bin (p, b, update l k ~f, r)
      | RB -> Bin (p, b, l, update r k ~f)
  [@@specialise]

  let change_aux k v f =
    f v |> Option.value_map ~default:Nil ~f:(singleton k)
  [@@specialise]

  let rec change t k ~f = match t with
    | Nil -> change_aux k None f
    | Tip (k', v') when K.equal k k' -> change_aux k (Some v') f
    | Tip (k', _) -> join t k' (change_aux k None f) k
    | Bin (p, b, l, r) -> match order k ~prefix:p ~bit:b with
      | NA -> join (change_aux k None f) k t p
      | LB -> Bin (p, b, change l k ~f, r)
      | RB -> Bin (p, b, l, change r k ~f)
  [@@specialise]

  let rec set t ~key ~data = match t with
    | Nil -> Tip (key, data)
    | Tip (k', _) when K.equal key k' -> Tip (key, data)
    | Tip (k', _) -> join t k' (Tip (key, data)) key
    | Bin (p, b, l, r) -> match order key ~prefix:p ~bit:b with
      | NA -> join (Tip (key, data)) key t p
      | LB -> Bin (p, b, set l ~key ~data, r)
      | RB -> Bin (p, b, l, set r ~key ~data)

  let rec add_multi t ~key ~data = match t with
    | Nil -> Tip (key, [data])
    | Tip (k', xs) when K.equal key k' -> Tip (key, data :: xs)
    | Tip (k', _) -> join t k' (Tip (key, [data])) key
    | Bin (p, b, l, r) -> match order key ~prefix:p ~bit:b with
      | NA -> join (Tip (key, [data])) key t p
      | LB -> Bin (p, b, add_multi l ~key ~data, r)
      | RB -> Bin (p, b, l, add_multi r ~key ~data)

  let rec add_exn t ~key ~data = match t with
    | Nil -> Tip (key, data)
    | Tip (k', _) when K.equal key k' -> raise Duplicate
    | Tip (k', _) -> join t k' (Tip (key, data)) key
    | Bin (p, b, l, r) -> match order key ~prefix:p ~bit:b with
      | NA -> join (Tip (key, data)) key t p
      | LB -> Bin (p, b, add_exn l ~key ~data, r)
      | RB -> Bin (p, b, l, add_exn r ~key ~data)

  let add t ~key ~data = try `Ok (add_exn t ~key ~data) with
    | Duplicate -> `Duplicate

  let rec remove t k = match t with
    | Nil -> Nil
    | Tip (k', _) when K.equal k k' -> Nil
    | Tip _ -> t
    | Bin (p, b, l, r) -> match order k ~prefix:p ~bit:b with
      | NA -> t
      | LB -> of_key p b (remove l k) r
      | RB -> of_key p b l (remove r k)

  let rec merge t1 t2 ~f = match t1, t2 with
    | Nil, t | t, Nil -> t
    | Tip (k, v1), t | t, Tip (k, v1) ->
      update t k ~f:(function
          | Some v2 -> f ~key:k v1 v2
          | None -> v1)
    | Bin (p1, b1, l1, r1), Bin (p2, b2, l2, r2) ->
      match order2 p1 b1 p2 b2 with
      | EQ -> of_key p1 b1 (merge l1 l2 ~f) (merge r1 r2 ~f)
      | LIL -> Bin (p1, b1, merge l1 t2 ~f, r1)
      | LIR -> Bin (p1, b1, l1, merge r1 t2 ~f)
      | RIL -> Bin (p2, b2, merge t1 l2 ~f, r2)
      | RIR -> Bin (p2, b2, l2, merge t1 r2 ~f)
      | DJ -> join t1 p1 t2 p2
  [@@specialise]

  let rec iter t ~f = match t with
    | Nil -> ()
    | Tip (k, v) -> f ~key:k ~data:v
    | Bin (_, _, l, r) -> iter l ~f; iter r ~f
  [@@specialise]

  let rec fold t ~init ~f = match t with
    | Nil -> init
    | Tip (k, v) -> f ~key:k ~data:v init
    | Bin (_, _, l, r) -> fold r ~f ~init:(fold l ~init ~f)
  [@@specialise]

  let rec fold_right t ~init ~f = match t with
    | Nil -> init
    | Tip (k, v) -> f ~key:k ~data:v init
    | Bin (_, _, l, r) -> fold_right l ~f ~init:(fold_right r ~init ~f)
  [@@specialise]

  let rec length = function
    | Nil -> 0
    | Tip _ -> 1
    | Bin (_, _, l, r) -> length l + length r

  let data t = fold_right t ~f:(fun ~key:_ ~data:x xs -> x :: xs) ~init:[]
  let keys t = fold_right t ~f:(fun ~key:x ~data:_ xs -> x :: xs) ~init:[]
  let to_list t = fold_right t ~f:(fun ~key ~data acc -> (key, data) :: acc) ~init:[]

  let of_alist_exn =
    List.fold ~init:empty ~f:(fun t (key, data) -> add_exn t ~key ~data)

  let of_alist l = try Some (of_alist_exn l) with
    | Duplicate -> None

  let to_sequence ?(order = `Increasing_key) =
    let open Seq.Generator in
    match order with
    | `Increasing_key ->
      let rec aux = function
        | Nil -> return ()
        | Tip (k, x) -> yield (k, x)
        | Bin (_, _, l, r) -> aux l >>= fun () -> aux r in
      fun t -> run @@ aux t
    | `Decreasing_key ->
      let rec aux = function
        | Nil -> return ()
        | Tip (k, x) -> yield (k, x)
        | Bin (_, _, l, r) -> aux r >>= fun () -> aux l in
      fun t -> run @@ aux t
  [@@specialise]

  let rec equal f t1 t2 = phys_equal t1 t2 || match t1, t2 with
    | Nil, Nil -> assert false
    | Tip (k1, x1), Tip (k2, x2) ->
      K.equal k1 k2 && f x1 x2
    | Bin (p1, b1, l1, r1), Bin (p2, b2, l2, r2) ->
      equal_prefix p1 b1 p2 b2 && equal f l1 l2 && equal f r1 r2
    | _ -> false

  let rec compare f t1 t2 =
    if phys_equal t1 t2 then 0 else match t1, t2 with
      | Nil, Nil -> assert false
      | Tip (k1, x1), Tip (k2, x2) ->
        let c = K.compare k1 k2 in
        if c = 0 then f x1 x2 else c
      | Bin (p1, b1, l1, r1), Bin (p2, b2, l2, r2) ->
        let c = compare_prefix p1 b1 p2 b2 in
        if c = 0 then
          let c = compare f l1 l2 in
          if c = 0 then compare f r1 r2 else c
        else c
      | Nil, _ -> 1
      | Tip _, Nil -> -1
      | Tip _, Bin _ -> 1
      | Bin _, _ -> -1
end

module Make_set(K : Patricia_tree_intf.Key) = struct
  type key = K.t

  open Make_helpers(K)

  type t =
    | Bin of key * key * t * t
    | Tip of key
    | Nil

  let empty = Nil

  let is_empty = function
    | Bin _ | Tip _ -> false
    | Nil -> true
  [@@inline]

  let rec mem t k = match t with
    | Nil -> false
    | Tip k' -> K.equal k k'
    | Bin (p, b, l, r) -> match order k ~prefix:p ~bit:b with
      | NA -> false
      | LB -> mem l k
      | RB -> mem r k

  let of_key p b l r = match l, r with
    | Nil, o | o, Nil -> o
    | _ -> Bin (p, b, l, r)

  let join t1 p1 t2 p2 =
    let bit = branching_bit p1 p2 in
    let m = mask p1 ~bit in
    if zero_bit p1 ~bit
    then of_key m bit t1 t2
    else of_key m bit t2 t1

  let singleton k = Tip k

  exception Empty

  let rec min_elt_exn = function
    | Nil -> raise Empty
    | Tip k -> k
    | Bin (_, _, l, r) ->
      try min_elt_exn l with
      | Empty -> min_elt_exn r

  let rec max_elt_exn = function
    | Nil -> raise Empty
    | Tip k -> k
    | Bin (_, _, l, r) ->
      try max_elt_exn r with
      | Empty -> max_elt_exn l

  let rec add t k = match t with
    | Nil -> Tip k
    | Tip k' when K.equal k' k -> t
    | Tip k' -> join t k' (Tip k) k
    | Bin (p, b, l, r) -> match order k ~prefix:p ~bit:b with
      | NA -> join (Tip k) k t p
      | LB -> Bin (p, b, add l k, r)
      | RB -> Bin (p, b, l, add r k)

  let rec remove t k = match t with
    | Nil -> Nil
    | Tip k' when K.equal k k' -> Nil
    | Tip _ -> t
    | Bin (p, b, l, r) -> match order k ~prefix:p ~bit:b with
      | NA -> t
      | LB -> of_key p b (remove l k) r
      | RB -> of_key p b l (remove r k)

  let rec union t1 t2 = match t1, t2 with
    | Nil, t | t, Nil -> t
    | Tip k, t | t, Tip k -> add t k
    | Bin (p1, b1, l1, r1), Bin (p2, b2, l2, r2) ->
      match order2 p1 b1 p2 b2 with
      | EQ -> of_key p1 b1 (union l1 l2) (union r1 r2)
      | LIL -> Bin (p1, b1, union l1 t2, r1)
      | LIR -> Bin (p1, b1, l1, union r1 t2)
      | RIL -> Bin (p2, b2, union t1 l2, r2)
      | RIR -> Bin (p2, b2, l2, union t1 r2)
      | DJ -> join t1 p1 t2 p2

  let rec inter t1 t2 = match t1, t2 with
    | Nil, _ | _, Nil -> Nil
    | Tip k, t when mem t k -> t1
    | Tip _, _ -> Nil
    | t, Tip k when mem t k -> t2
    | _, Tip _ -> Nil
    | Bin (p1, b1, l1, r1), Bin (p2, b2, l2, r2) ->
      match order2 p1 b1 p2 b2 with
      | EQ -> of_key p1 b1 (inter l1 l2) (inter r1 r2)
      | LIL -> inter l1 t2
      | LIR -> inter r1 t2
      | RIL -> inter t1 l2
      | RIR -> inter t1 r2
      | DJ -> Nil

  let rec disjoint t1 t2 = match t1, t2 with
    | Nil, _ | _, Nil -> true
    | Tip k, t | t, Tip k -> not @@ mem t k
    | Bin (p1, b1, l1, r1), Bin (p2, b2, l2, r2) ->
      match order2 p1 b1 p2 b2 with
      | EQ -> disjoint l1 l2 && disjoint r1 r2
      | LIL -> disjoint l1 t2
      | LIR -> disjoint r1 t2
      | RIL -> disjoint t1 l2
      | RIR -> disjoint t1 r2
      | DJ -> true

  let rec iter t ~f = match t with
    | Nil -> ()
    | Tip k -> f k
    | Bin (_, _, l, r) -> iter l ~f; iter r ~f
  [@@specialise]

  let rec fold t ~init ~f = match t with
    | Nil -> init
    | Tip k -> f init k
    | Bin (_, _, l, r) -> fold r ~f ~init:(fold l ~init ~f)
  [@@specialise]

  let rec fold_right t ~init ~f = match t with
    | Nil -> init
    | Tip k -> f k init
    | Bin (_, _, l, r) -> fold_right l ~f ~init:(fold_right r ~init ~f)
  [@@specialise]

  let rec length = function
    | Nil -> 0
    | Tip _ -> 1
    | Bin (_, _, l, r) -> length l + length r

  let map t ~f = fold t ~init:empty ~f:(fun t x -> add t @@ f x)
  let to_list t = fold_right t ~f:List.cons ~init:[]
  let of_list = List.fold ~init:empty ~f:add

  let to_sequence ?(order = `Increasing) =
    let open Seq.Generator in
    match order with
    | `Increasing ->
      let rec aux = function
        | Nil -> return ()
        | Tip k -> yield k
        | Bin (_, _, l, r) -> aux l >>= fun () -> aux r in
      fun t -> run @@ aux t
    | `Decreasing ->
      let rec aux = function
        | Nil -> return ()
        | Tip k -> yield k
        | Bin (_, _, l, r) -> aux r >>= fun () -> aux l in
      fun t -> run @@ aux t
  [@@specialise]

  let rec equal t1 t2 = phys_equal t1 t2 || match t1, t2 with
    | Nil, Nil -> assert false
    | Tip k1, Tip k2 -> K.equal k1 k2
    | Bin (p1, b1, l1, r1), Bin (p2, b2, l2, r2) ->
      equal_prefix p1 b1 p2 b2 && equal l1 l2 && equal r1 r2
    | _ -> false

  let rec compare t1 t2 =
    if phys_equal t1 t2 then 0 else match t1, t2 with
      | Nil, Nil -> assert false
      | Tip k1, Tip k2 -> K.compare k1 k2
      | Bin (p1, b1, l1, r1), Bin (p2, b2, l2, r2) ->
        let c = compare_prefix p1 b1 p2 b2 in
        if c = 0 then
          let c = compare l1 l2 in
          if c = 0 then compare r1 r2 else c
        else c
      | Nil, _ -> 1
      | Tip _, Nil -> -1
      | Tip _, Bin _ -> 1
      | Bin _, _ -> -1

  let of_sequence = Seq.fold ~init:empty ~f:add
end
