open Core
open Regular.Std

module Make_helpers(K : Patricia_tree_intf.Key) = struct
  open K

  let _ = pp (* silence warning *)

  let mask ~bit x =
    let m = one lsl to_int bit in
    (x lor (m - one)) land (lnot m)

  let clz v = of_int @@ clz v [@@inline]
  let numbits v = of_int size - clz v [@@inline]
  let highest_bit x = numbits x - one
  let is_zero ~bit x = equal (x land (one lsl to_int bit)) zero
end

module Make_key(K : Patricia_tree_intf.Key) = struct
  open K

  let _ = pp (* silence warning *)

  type nonrec t = {key : t} [@@unboxed]

  (* Currently `Base.Int64.popcount` and `Base.Int.ceil_pow2` are
     implemented by hand instead of calling out to C stubs, so the
     OCaml compiler has a chance to do some constant folding assuming
     that the user provided `K.size` as a known constant. *)
  let ctz x =
    let x = Int.(to_int64 ((lnot x) land (pred x))) in
    Int64.popcount x

  let branching_size = ctz @@ Int.ceil_pow2 size
  let payload_size = Int.(size - branching_size)
  let branching_mask = ((one lsl branching_size) - one) lsl payload_size
  let payload_mask = (one lsl payload_size) - one
  let branching {key} = (key land branching_mask) lsr payload_size [@@inline]
  let payload {key} = key land payload_mask [@@inline]

  let create ~branching ~payload = {
    key = (branching lsl payload_size) lor payload
  }

  type order = NA | LB | RB

  let compare k k' =
    let x = payload k in
    let bit = branching k in
    let m = one lsl to_int bit in
    let y = (k' lor (m - one)) land (lnot m) in
    match equal x y with
    | true when equal (k' land m) zero -> LB
    | true -> RB
    | false -> NA
  [@@inline]

  let equal {key = k1} {key = k2} = equal k1 k2 [@@inline]
end

(* Implementation of a PATRICIA tree, adapted from BAP:

   https://github.com/BinaryAnalysisPlatform/bap/blob/517db3d15ee98e914cd970ab4a9bf4d17b65ee35/lib/knowledge/bap_knowledge.ml#L82
*)
module Make(K : Patricia_tree_intf.Key) = struct
  open K

  let _ = pp (* silence warning *)

  type key = t

  open Make_helpers(K)

  module Key = Make_key(K)

  type +'a t =
    | Bin of Key.t * 'a t * 'a t
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

  let branching_bit a b = highest_bit (a lxor b)

  exception Not_found
  exception Duplicate

  let rec find_exn t k = match t with
    | Nil -> raise Not_found
    | Tip (k', v) when equal k k' -> v
    | Tip _ -> raise Not_found
    | Bin (k', l, r) -> match Key.compare k' k with
      | NA -> raise Not_found
      | LB -> find_exn l k
      | RB -> find_exn r k

  let find t k = try Some (find_exn t k) with
    | Not_found -> None

  let mem t k = try ignore (find_exn t k); true with
    | Not_found -> false

  let node payload branching l r = match l, r with
    | Nil, o | o, Nil -> o
    | _ -> Bin (Key.create ~branching ~payload, l, r)

  let of_key key l r = match l, r with
    | Nil, o | o, Nil -> o
    | _ -> Bin (key, l, r)

  let join t1 p1 t2 p2 =
    let switch = branching_bit p1 p2 in
    let prefix = mask p1 ~bit:switch in
    if is_zero p1 ~bit:switch
    then node prefix switch t1 t2
    else node prefix switch t2 t1

  let singleton k v = Tip (k, v)

  let rec update_with t k ~has ~nil = match t with
    | Nil -> Tip (k, nil ())
    | Tip (k', v') when equal k k' -> Tip (k, has v')
    | Tip (k', _) -> join t k' (Tip (k, nil ())) k
    | Bin (k', l, r) -> match Key.compare k' k with
      | NA -> join (Tip (k, nil ())) k t (Key.payload k')
      | LB -> Bin (k', update_with l k ~has ~nil, r)
      | RB -> Bin (k', l, update_with r k ~has ~nil)
  [@@specialise]

  let rec update t k ~f = match t with
    | Nil -> Tip (k, f None)
    | Tip (k', v') when equal k k' -> Tip (k, f (Some v'))
    | Tip (k', _) -> join t k' (Tip (k, f None)) k
    | Bin (k', l, r) -> match Key.compare k' k with
      | NA -> join (Tip (k, f None)) k t (Key.payload k')
      | LB -> Bin (k', update l k ~f, r)
      | RB -> Bin (k', l, update r k ~f)
  [@@specialise]

  let change_aux k v f =
    f v |> Option.value_map ~default:Nil ~f:(singleton k)
  [@@specialise]

  let rec change t k ~f = match t with
    | Nil -> change_aux k None f
    | Tip (k', v') when equal k k' -> change_aux k (Some v') f
    | Tip (k', _) -> join t k' (change_aux k None f) k
    | Bin (k', l, r) -> match Key.compare k' k with
      | NA -> join (change_aux k None f) k t (Key.payload k')
      | LB -> Bin (k', change l k ~f, r)
      | RB -> Bin (k', l, change r k ~f)
  [@@specialise]

  let rec set t ~key ~data = match t with
    | Nil -> Tip (key, data)
    | Tip (k', _) when equal key k' -> Tip (key, data)
    | Tip (k', _) -> join t k' (Tip (key, data)) key
    | Bin (k', l, r) -> match Key.compare k' key with
      | NA -> join (Tip (key, data)) key t (Key.payload k')
      | LB -> Bin (k', set l ~key ~data, r)
      | RB -> Bin (k', l, set r ~key ~data)

  let rec add_multi t ~key ~data = match t with
    | Nil -> Tip (key, [data])
    | Tip (k', xs) when equal key k' -> Tip (key, data :: xs)
    | Tip (k', _) -> join t k' (Tip (key, [data])) key
    | Bin (k', l, r) -> match Key.compare k' key with
      | NA -> join (Tip (key, [data])) key t (Key.payload k')
      | LB -> Bin (k', add_multi l ~key ~data, r)
      | RB -> Bin (k', l, add_multi r ~key ~data)

  let rec add_exn t ~key ~data = match t with
    | Nil -> Tip (key, data)
    | Tip (k', _) when equal key k' -> raise Duplicate
    | Tip (k', _) -> join t k' (Tip (key, data)) key
    | Bin (k', l, r) -> match Key.compare k' key with
      | NA -> join (Tip (key, data)) key t (Key.payload k')
      | LB -> Bin (k', add_exn l ~key ~data, r)
      | RB -> Bin (k', l, add_exn r ~key ~data)

  let add t ~key ~data = try `Ok (add_exn t ~key ~data) with
    | Duplicate -> `Duplicate

  let rec remove t k = match t with
    | Nil -> Nil
    | Tip (k', _) -> if equal k k' then Nil else t
    | Bin (k', l, r) -> match Key.compare k' k with
      | NA -> t
      | LB -> of_key k' (remove l k) r
      | RB -> of_key k' l (remove r k)

  let rec merge t1 t2 ~f = match t1, t2 with
    | Nil, t | t, Nil -> t
    | Tip (k, v1), t | t, Tip (k, v1) ->
      update t k ~f:(function
          | Some v2 -> f ~key:k v1 v2
          | None -> v1)
    | Bin (p1, l1, r1), Bin (p2, l2, r2) when Key.equal p1 p2 ->
      of_key p1 (merge l1 l2 ~f) (merge r1 r2 ~f)
    | Bin (p1, l1, r1), Bin (p2, l2, r2) ->
      let k1 = Key.payload p1 in
      let k2 = Key.payload p2 in
      let b1 = Key.branching p1 in
      let b2 = Key.branching p2 in
      match Key.compare p1 k2 with
      | RB -> if is_zero ~bit:b1 k2
        then Bin (p1, merge l1 t2 ~f, r1)
        else Bin (p1, l1, merge r1 t2 ~f)
      | LB -> if is_zero ~bit:b2 k1
        then Bin (p2, merge t1 l2 ~f, r2)
        else Bin (p2, l2, merge t1 r2 ~f)
      | NA -> match Key.compare p2 k1 with
        | NA -> join t1 k1 t2 k2
        | RB -> Bin (p2, l2, merge t1 r2 ~f)
        | LB -> Bin (p2, merge t1 l2 ~f, r2)
  [@@specialise]

  let rec iter t ~f = match t with
    | Nil -> ()
    | Tip (k, v) -> f ~key:k ~data:v
    | Bin (_, l, r) -> iter l ~f; iter r ~f
  [@@specialise]

  let rec fold t ~init ~f = match t with
    | Nil -> init
    | Tip (k, v) -> f ~key:k ~data:v init
    | Bin (_, l, r) -> fold r ~f ~init:(fold l ~init ~f)
  [@@specialise]

  let rec fold_right t ~init ~f = match t with
    | Nil -> init
    | Tip (k, v) -> f ~key:k ~data:v init
    | Bin (_, l, r) -> fold_right l ~f ~init:(fold_right r ~init ~f)
  [@@specialise]

  let rec length = function
    | Nil -> 0
    | Tip _ -> 1
    | Bin (_, l, r) -> length l + length r

  let data t = fold_right t ~f:(fun ~key:_ ~data:x xs -> x :: xs) ~init:[]
  let keys t = fold_right t ~f:(fun ~key:x ~data:_ xs -> x :: xs) ~init:[]

  let of_alist_exn =
    List.fold ~init:empty ~f:(fun t (key, data) -> add_exn t ~key ~data)

  let of_alist l = Option.try_with @@ fun () -> of_alist_exn l

  let to_list t =
    let rec aux acc = function
      | Nil -> acc
      | Tip (k, x) -> (k, x) :: acc
      | Bin (_, l, r) -> aux (aux acc r) l in
    aux [] t

  let to_sequence ?(order = `Increasing_key) =
    let open Seq.Generator in
    match order with
    | `Increasing_key ->
      let rec aux = function
        | Nil -> return ()
        | Tip (k, x) -> yield (k, x)
        | Bin (_, l, r) -> aux l >>= fun () -> aux r in
      fun t -> run @@ aux t
    | `Decreasing_key ->
      let rec aux = function
        | Nil -> return ()
        | Tip (k, x) -> yield (k, x)
        | Bin (_, l, r) -> aux r >>= fun () -> aux l in
      fun t -> run @@ aux t

  let equal f t1 t2 =
    Seq.equal (fun (k1, v1) (k2, v2) -> K.equal k1 k2 && f v1 v2)
      (to_sequence t1) (to_sequence t2)

  let compare f t1 t2 =
    Seq.compare (fun (k1, v1) (k2, v2) ->
        match K.compare k1 k2 with
        | 0 -> f v1 v2
        | n -> n)
      (to_sequence t1) (to_sequence t2)
end

module Make_set(K : Patricia_tree_intf.Key) = struct
  open K

  let _ = pp (* silence warning *)

  type key = t

  open Make_helpers(K)

  module Key = Make_key(K)

  type t =
    | Bin of Key.t * t * t
    | Tip of key
    | Nil

  let empty = Nil

  let is_empty = function
    | Bin _ | Tip _ -> false
    | Nil -> true
  [@@inline]

  let branching_bit a b = highest_bit (a lxor b)

  let rec mem t k = match t with
    | Nil -> false
    | Tip k' -> equal k k'
    | Bin (k', l, r) -> match Key.compare k' k with
      | NA -> false
      | LB -> mem l k
      | RB -> mem r k

  let node payload branching l r = match l, r with
    | Nil, o | o, Nil -> o
    | _ -> Bin (Key.create ~branching ~payload, l, r)

  let of_key key l r = match l, r with
    | Nil, o | o, Nil -> o
    | _ -> Bin (key, l, r)

  let join t1 p1 t2 p2 =
    let switch = branching_bit p1 p2 in
    let prefix = mask p1 ~bit:switch in
    if is_zero p1 ~bit:switch
    then node prefix switch t1 t2
    else node prefix switch t2 t1

  let singleton k = Tip k

  exception Empty

  let rec min_elt_exn = function
    | Nil -> raise Empty
    | Tip k -> k
    | Bin (_, l, r) ->
      try min_elt_exn l with
      | Empty -> min_elt_exn r

  let rec max_elt_exn = function
    | Nil -> raise Empty
    | Tip k -> k
    | Bin (_, l, r) ->
      try max_elt_exn r with
      | Empty -> max_elt_exn l

  let rec add t k = match t with
    | Nil -> Tip k
    | Tip k' when equal k' k -> t
    | Tip k' -> join t k' (Tip k) k
    | Bin (k', l, r) -> match Key.compare k' k with
      | NA -> join (Tip k) k t (Key.payload k')
      | LB -> Bin (k', add l k, r)
      | RB -> Bin (k', l, add r k)

  let rec remove t k = match t with
    | Nil -> Nil
    | Tip k' -> if equal k k' then Nil else t
    | Bin (k', l, r) -> match Key.compare k' k with
      | NA -> t
      | LB -> of_key k' (remove l k) r
      | RB -> of_key k' l (remove r k)

  let rec union t1 t2 = match t1, t2 with
    | Nil, t | t, Nil -> t
    | Tip k, t | t, Tip k -> add t k
    | Bin (p1, l1, r1), Bin (p2, l2, r2) when Key.equal p1 p2 ->
      of_key p1 (union l1 l2) (union r1 r2)
    | Bin (p1, l1, r1), Bin (p2, l2, r2) ->
      let k1 = Key.payload p1 in
      let k2 = Key.payload p2 in
      let b1 = Key.branching p1 in
      let b2 = Key.branching p2 in
      match Key.compare p1 k2 with
      | RB -> if is_zero ~bit:b1 k2
        then Bin (p1, union l1 t2, r1)
        else Bin (p1, l1, union r1 t2)
      | LB -> if is_zero ~bit:b2 k1
        then Bin (p2, union t1 l2, r2)
        else Bin (p2, l2, union t1 r2)
      | NA -> match Key.compare p2 k1 with
        | NA -> join t1 k1 t2 k2
        | LB -> Bin (p2, union t1 l2, r2)
        | RB -> Bin (p2, l2, union t1 r2)

  let rec inter_key k t = match t with
    | Nil -> Nil
    | Tip k' when equal k k' -> t
    | Tip _ -> Nil
    | Bin (p, l, r) -> match Key.compare p k with
      | NA -> Nil
      | LB -> inter_key k l
      | RB -> inter_key k r

  let rec inter t1 t2 = match t1, t2 with
    | Nil, _ | _, Nil -> Nil
    | Tip k, t | t, Tip k -> inter_key k t
    | Bin (p1, l1, r1), Bin (p2, l2, r2) when Key.equal p1 p2 ->
      of_key p1 (inter l1 l2) (inter r1 r2)
    | Bin (p1, l1, r1), Bin (p2, l2, r2) ->
      let k1 = Key.payload p1 in
      let k2 = Key.payload p2 in
      let b1 = Key.branching p1 in
      let b2 = Key.branching p2 in
      match Key.compare p1 k2 with
      | NA -> Nil
      | RB -> if is_zero ~bit:b1 k2
        then inter l1 t2
        else inter r1 t2
      | LB -> if is_zero ~bit:b2 k1
        then inter t1 l2
        else inter t1 r2

  let rec disjoint t1 t2 = match t1, t2 with
    | Nil, _ | _, Nil -> true
    | Tip k, t | t, Tip k -> not @@ mem t k
    | Bin (p1, l1, r1), Bin (p2, l2, r2) when Key.equal p1 p2 ->
      disjoint l1 l2 && disjoint r1 r2
    | Bin (p1, l1, r1), Bin (p2, l2, r2) ->
      let k1 = Key.payload p1 in
      let k2 = Key.payload p2 in
      let b1 = Key.branching p1 in
      let b2 = Key.branching p2 in
      match Key.compare p1 k2 with
      | NA -> true
      | RB -> if is_zero ~bit:b1 k2
        then disjoint l1 t2
        else disjoint r1 t2
      | LB -> if is_zero ~bit:b2 k1
        then disjoint t1 l2
        else disjoint t1 r2

  let rec iter t ~f = match t with
    | Nil -> ()
    | Tip k -> f k
    | Bin (_, l, r) -> iter l ~f; iter r ~f
  [@@specialise]

  let rec fold t ~init ~f = match t with
    | Nil -> init
    | Tip k -> f init k
    | Bin (_, l, r) -> fold r ~f ~init:(fold l ~init ~f)
  [@@specialise]

  let rec fold_right t ~init ~f = match t with
    | Nil -> init
    | Tip k -> f k init
    | Bin (_, l, r) -> fold_right l ~f ~init:(fold_right r ~init ~f)
  [@@specialise]

  let rec length = function
    | Nil -> 0
    | Tip _ -> 1
    | Bin (_, l, r) -> length l + length r

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
        | Bin (_, l, r) -> aux l >>= fun () -> aux r in
      fun t -> run @@ aux t
    | `Decreasing ->
      let rec aux = function
        | Nil -> return ()
        | Tip k -> yield k
        | Bin (_, l, r) -> aux r >>= fun () -> aux l in
      fun t -> run @@ aux t

  let equal t1 t2 =
    Seq.equal K.equal (to_sequence t1) (to_sequence t2)

  let compare t1 t2 =
    Seq.compare K.compare (to_sequence t1) (to_sequence t2)

  let of_sequence = Seq.fold ~init:empty ~f:add
end
