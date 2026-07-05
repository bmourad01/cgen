open Core

let bits_per_level = 5
let branch_mask = (1 lsl bits_per_level) - 1

let bitpos i = 1 lsl i [@@inline]
let has_bit m i = (m land bitpos i) <> 0 [@@inline]
let rank m i = Int.popcount (m land (bitpos i - 1)) [@@inline]
let index h sh = (h lsr sh) land branch_mask [@@inline]

let array_insert a i x =
  let n = Array.length a in
  if i = n then
    (* Insert at end *)
    let a' = Array.create ~len:(n + 1) x in
    Array.unsafe_blit ~src:a ~src_pos:0 ~dst:a' ~dst_pos:0 ~len:n;
    a'
  else if i = 0 then
    (* Insert at beginning. *)
    let a' = Array.create ~len:(n + 1) x in
    Array.unsafe_blit ~src:a ~src_pos:0 ~dst:a' ~dst_pos:1 ~len:n;
    a'
  else
    (* Insert in the middle. *)
    let () = assert (i >= 1 && i < n) in
    let a' = Array.create ~len:(n + 1) x in
    Array.unsafe_blit ~src:a ~src_pos:0 ~dst:a' ~dst_pos:0 ~len:i;
    Array.unsafe_blit ~src:a ~src_pos:i ~dst:a' ~dst_pos:(i + 1) ~len:(n - i);
    a'

let array_update a i x =
  let a' = Array.copy a in
  a'.(i) <- x;
  a'
[@@inline]

let array_remove a i =
  let n = Array.length a in
  assert (i >= 0 && i < n);
  if n = 1 then [||] (* Singleton fast path. *)
  else if i = n - 1 then
    (* Delete from the end. *)
    Array.sub a ~pos:0 ~len:(n - 1)
  else if i = 0 then
    (* Delete from the beginning. *)
    Array.sub a ~pos:1 ~len:(n - 1)
  else
    (* Delete from the middle. *)
    let a' = Array.create ~len:(n - 1) a.(0) in
    Array.unsafe_blit ~src:a ~src_pos:0 ~dst:a' ~dst_pos:0 ~len:i;
    Array.unsafe_blit ~src:a ~src_pos:(i + 1) ~dst:a' ~dst_pos:i ~len:(n - i - 1);
    a'

let array_iter a ~f = Array.iter a ~f:(fun (_, v) -> f v)
let array_iteri a ~f = Array.iter a ~f:(fun (k, v) -> f ~key:k ~data:v)

let array_fold a ~init ~f =
  Array.fold a ~init ~f:(fun acc (_, v) -> f acc v)

let array_foldi a ~init ~f =
  Array.fold a ~init ~f:(fun acc (k, v) -> f ~key:k ~data:v acc)

let hash_fold_array f state t =
  Array.fold t ~init:(hash_fold_int state (Array.length t)) ~f

module Make(K : Champ_intf.Key) = struct
  type key = K.t [@@deriving bin_io, compare, equal, hash, sexp]
  type 'a entries = (key * 'a) array [@@deriving bin_io, compare, equal, hash, sexp]

  (* [Empty]: empty node

     [Collision {hash; entries}]: collision at [hash], with
     bucket of [entries]

     [Bucket {entries}]: not for collisions, but for when we've reached
     the maximum depth of the tree

     [Node {...}]: a regular node. Note that [data] is not sorted by
     key; this is instead indexed by "rank", based on the hash and
     current depth in the tree.

     Note: in the case of a [Collision] or [Bucket], the [entries] array
     is sorted, which keeps the worst case search time at O(log n).

     The [Collision] and [Bucket] entries are intended to be small, except
     in the case of adversarial inputs (i.e. a pathologically bad hash
     function for `key`).
  *)
  type 'a t =
    | Empty
    | Collision of {
        entries : 'a entries;
        hash    : int;
      }
    | Bucket of {
        entries : 'a entries;
      }
    | Node of {
        data_map : int;
        node_map : int;
        data     : 'a entries;
        children : 'a t array;
      }
  [@@deriving bin_io, compare, equal, hash, sexp]

  exception Not_found
  exception Duplicate

  let empty = Empty

  let find_index a k =
    Binary_search.binary_search a
      ~get:(fun a i -> fst a.(i))
      ~length:Array.length
      ~compare:K.compare
      `First_equal_to k

  let find_insert_index a k =
    Binary_search.binary_search a
      ~get:(fun a i -> fst a.(i))
      ~length:Array.length
      ~compare:K.compare
      `First_greater_than_or_equal_to k

  let array_update_kv a k ~has ~nil = match find_insert_index a k with
    | None -> array_insert a (Array.length a) (k, nil ())
    | Some i ->
      let k', v = a.(i) in
      if equal_key k k'
      then array_update a i (k, has v)
      else array_insert a i (k, nil ())
  [@@specialise]

  let array_remove_kv a k = match find_index a k with
    | Some i -> array_remove a i
    | None -> a

  let find_sorted a k =
    find_index a k |> Option.map ~f:(fun i -> snd a.(i))

  let rec find t k h sh = match t with
    | Empty -> None
    | Collision c when c.hash <> h -> None
    | Collision {entries = a; _}
    | Bucket {entries = a} -> find_sorted a k
    | Node n ->
      let i = index h sh in
      if has_bit n.data_map i then
        let d = rank n.data_map i in
        let k', v = n.data.(d) in
        if equal_key k k' then Some v else None
      else if has_bit n.node_map i then
        let c = rank n.node_map i in
        find n.children.(c) k h (sh + bits_per_level)
      else None

  let rec mem t k h sh = match t with
    | Empty -> false
    | Collision c when c.hash <> h -> false
    | Collision {entries = a; _}
    | Bucket {entries = a} ->
      Option.is_some (find_index a k)
    | Node n ->
      let i = index h sh in
      if has_bit n.data_map i then
        let d = rank n.data_map i in
        let k', _ = n.data.(d) in
        equal_key k k'
      else if has_bit n.node_map i then
        let c = rank n.node_map i in
        mem n.children.(c) k h (sh + bits_per_level)
      else false

  let merge_two_bucket k1 v1 k2 v2 =
    if K.compare k1 k2 <= 0
    then [|k1, v1; k2, v2|]
    else [|k2, v2; k1, v1|]

  (* pre: k1 and k2 are not equal *)
  let rec merge_two k1 v1 h1 k2 v2 h2 sh =
    if h1 = h2 then
      Collision {hash = h1; entries = merge_two_bucket k1 v1 k2 v2}
    else if sh > Sys.int_size_in_bits - bits_per_level then
      Bucket {entries = merge_two_bucket k1 v1 k2 v2}
    else
      let i1 = index h1 sh in
      let i2 = index h2 sh in
      if i1 <> i2 then
        let data = if i1 < i2
          then [|k1, v1; k2, v2|]
          else [|k2, v2; k1, v1|] in
        Node {
          data_map = bitpos i1 lor bitpos i2;
          node_map = 0;
          data;
          children = [||];
        }
      else
        Node {
          data_map = 0;
          node_map = bitpos i1;
          data = [||];
          children = [|
            merge_two k1 v1 h1 k2 v2 h2 (sh + bits_per_level);
          |];
        }

  let singleton k v h sh = Node {
      data_map = bitpos (index h sh);
      node_map = 0;
      data = [|k, v|];
      children = [||];
    }

  let rec upsert ~has ~nil t k h sh = match t with
    | Empty -> singleton k (nil ()) h sh
    | Collision c when c.hash = h ->
      Collision {c with entries = array_update_kv c.entries k ~has ~nil}
    | Collision {entries = a; _} | Bucket {entries = a} ->
      (* Depth exhausted, so downgrade to a catch-all bucket. *)
      Bucket {entries = array_update_kv a k ~has ~nil}
    | Node n ->
      let i = index h sh in
      let b = bitpos i in
      if has_bit n.data_map i then
        let d = rank n.data_map i in
        let k', v' = n.data.(d) in
        if equal_key k k' then
          Node {n with data = array_update n.data d (k, has v')}
        else
          let h' = K.hash k' and v = nil () in
          let child = merge_two k' v' h' k v h (sh + bits_per_level) in
          Node {
            data_map = n.data_map land lnot b;
            node_map = n.node_map lor b;
            data = array_remove n.data d;
            children = array_insert n.children (rank n.node_map i) child;
          }
      else if has_bit n.node_map i then
        let c = rank n.node_map i in
        let child' = upsert ~has ~nil n.children.(c) k h (sh + bits_per_level) in
        Node {n with children = array_update n.children c child'}
      else
        Node {
          n with
          data_map = n.data_map lor b;
          data = array_insert n.data (rank n.data_map i) (k, nil ());
        }
  [@@specialise]

  let collapse_singleton_bucket entries h sh = Node {
      data_map = bitpos (index h sh);
      node_map = 0;
      data = entries;
      children = [||];
    }
  [@@inline]

  let collapse_singleton_node
      node_map data_map data children
      ~i ~b ~c ~k ~v = Node {
      node_map = node_map land lnot b;
      data_map = data_map lor b;
      children = array_remove children c;
      data = array_insert data (rank data_map i) (k, v);
    }
  [@@inline]

  let rec remove t k h sh = match t with
    | Empty -> Empty
    | Collision c when c.hash <> h -> t
    | Collision c ->
      let entries = array_remove_kv c.entries k in
      let n = Array.length entries in
      if n <= 0 then Empty
      else if n > 1 then Collision {c with entries}
      else collapse_singleton_bucket entries h sh
    | Bucket b ->
      let entries = array_remove_kv b.entries k in
      let n = Array.length entries in
      if n <= 0 then Empty
      else if n > 1 then Bucket {entries}
      else collapse_singleton_bucket entries h sh
    | Node n ->
      let i = index h sh in
      let b = bitpos i in
      if has_bit n.data_map i then
        let d = rank n.data_map i in
        let k', _ = n.data.(d) in
        if not (equal_key k k') then t else
          let data = array_remove n.data d in
          let data_map = n.data_map land lnot b in
          if data_map = 0 && n.node_map = 0 then Empty
          else Node {n with data_map; data}
      else if has_bit n.node_map i then
        let c = rank n.node_map i in
        let child = n.children.(c) in
        match remove child k h (sh + bits_per_level) with
        | Empty ->
          let node_map = n.node_map land lnot b in
          let children = array_remove n.children c in
          if node_map = 0 && n.data_map = 0 then Empty
          else Node {n with node_map; children}
        | Node {node_map = 0; data = [|k', v'|]; _} ->
          collapse_singleton_node ~i ~b ~c ~k:k' ~v:v'
            n.node_map n.data_map n.data n.children
        | (Node _ | Collision _ | Bucket _) as child' ->
          Node {n with children = array_update n.children c child'}
      else t

  let find t k = find t k (K.hash k) 0 [@@inline]

  let find_exn t k = match find t k with
    | None -> raise Not_found
    | Some v -> v
  [@@inline]

  let mem t k = mem t k (K.hash k) 0 [@@inline]

  let set t ~key ~data =
    upsert t key (K.hash key) 0
      ~has:(Fn.const data)
      ~nil:(Fn.const data)
  [@@inline]

  let add_exn t ~key ~data =
    upsert t key (K.hash key) 0
      ~has:(fun _ -> raise Duplicate)
      ~nil:(fun () -> data)
  [@@inline]

  let add t ~key ~data = try `Ok (add_exn t ~key ~data) with
    | Duplicate -> `Duplicate
  [@@inline]

  let remove t k =
    if mem t k then remove t k (K.hash k) 0 else t [@@inline]

  let update t k ~f =
    upsert t k (K.hash k) 0
      ~has:(fun v -> f (Some v))
      ~nil:(fun () -> f None)
  [@@inline]

  let update_with t k ~has ~nil = upsert t k (K.hash k) 0 ~has ~nil [@@inline]

  let rec iter t ~f = match t with
    | Empty -> ()
    | Collision {entries = a; _}
    | Bucket {entries = a} -> array_iter a ~f
    | Node n ->
      array_iter n.data ~f;
      Array.iter n.children ~f:(iter ~f)

  let rec iteri t ~f = match t with
    | Empty -> ()
    | Collision {entries = a; _}
    | Bucket {entries = a} -> array_iteri a ~f
    | Node n ->
      array_iteri n.data ~f;
      Array.iter n.children ~f:(iteri ~f)

  let rec fold t ~init ~f = match t with
    | Empty -> init
    | Collision {entries = a; _}
    | Bucket {entries = a} -> array_fold a ~init ~f
    | Node n ->
      let init = array_fold n.data ~init ~f in
      Array.fold n.children ~init ~f:(fun init c -> fold c ~init ~f)

  let rec foldi t ~init ~f = match t with
    | Empty -> init
    | Collision {entries = a; _}
    | Bucket {entries = a} -> array_foldi a ~init ~f
    | Node n ->
      let init = array_foldi n.data ~init ~f in
      Array.fold n.children ~init ~f:(fun init c -> foldi c ~init ~f)

  let to_alist t = foldi t ~init:[] ~f:(fun ~key ~data acc -> (key, data) :: acc)
  let keys t = foldi t ~init:[] ~f:(fun ~key ~data:_ acc -> key :: acc)
  let data t = fold t ~init:[] ~f:(fun acc v -> v :: acc)

  let to_sequence t =
    let open Sequence.Generator in
    let rec go = function
      | Empty -> return ()
      | Collision {entries = a; _}
      | Bucket {entries = a; _} ->
        of_sequence (Array.to_sequence_mutable a)
      | Node n ->
        of_sequence (Array.to_sequence_mutable n.data) >>= fun () ->
        child n.children 0
    and child cs i =
      if i >= Array.length cs then return () else
        go cs.(i) >>= fun () ->
        child cs (i + 1) in
    run @@ go t

  let singleton k v = singleton k v (K.hash k) 0 [@@inline]

  let of_alist_exn l =
    List.fold l ~init:Empty ~f:(fun t (k, v) -> add_exn t ~key:k ~data:v)

  let of_alist l = try `Ok (of_alist_exn l) with
    | Duplicate -> `Duplicate

  let of_alist_overwrite l =
    List.fold l ~init:Empty ~f:(fun t (k, v) -> set t ~key:k ~data:v)

  let rec length = function
    | Empty -> 0
    | Collision {entries = a; _}
    | Bucket {entries = a} -> Array.length a
    | Node n ->
      Array.fold n.children
        ~init:(Array.length n.data)
        ~f:(fun n c -> n + length c)
end
