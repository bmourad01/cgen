(** An immutable, ordered map optimized for very small sizes.

    A height-balanced (AVL) tree with fat leaves: [T0..T4] hold 0 to 4 entries
    inline (so a map of at most four elements is a single heap block with no
    internal nodes), and [BR (h, l, k, v, r)] is a balanced internal node
    carrying its own height, with [|height l - height r| <= 1]. A subtree of at
    most four elements is always a leaf, so no [BR] ever has a [T0] child.

    The leaf shape is adapted from BAP's Knowledge Base; the internal nodes are
    a standard AVL with the height stored in the node.
*)

open Core
open Small_map_intf

module Make(Key : Key) : S with type key = Key.t = struct
  type key = Key.t [@@deriving compare, equal, sexp]

  type 'a t =
    | T0
    | T1 of key * 'a
    | T2 of key * 'a * key * 'a
    | T3 of key * 'a * key * 'a * key * 'a
    | T4 of key * 'a * key * 'a * key * 'a * key * 'a
    | BR of int * 'a t * key * 'a * 'a t
    (* height, left, pivot-key, pivot-value, right *)

  exception Not_found
  exception Duplicate

  module KI = struct
    type point = key
    type t = point * point
    let lo = fst
    let hi = snd
    let (<)  a b = Key.compare a b <  0
    let (>)  a b = Key.compare a b >  0
    let (<=) a b = Key.compare a b <= 0
    let (>=) a b = Key.compare a b >= 0
    let (=)  a b = Key.compare a b =  0
    let (<>) a b = Key.compare a b <> 0
  end

  module AP = Cgen_utils.Allen_point_algebra.Make(KI)
  module AI = Cgen_utils.Allen_interval_algebra.Make(KI)

  let empty = T0

  let is_empty = function
    | T0 -> true
    | _ -> false
  [@@inline]

  let singleton k v = T1 (k, v) [@@inline]

  let make1 k v = T1 (k, v) [@@inline]
  let make2 k1 v1 k2 v2 = T2 (k1, v1, k2, v2) [@@inline]
  let make3 k1 v1 k2 v2 k3 v3 = T3 (k1, v1, k2, v2, k3, v3) [@@inline]
  let make4 k1 v1 k2 v2 k3 v3 k4 v4 =
    T4 (k1, v1, k2, v2, k3, v3, k4, v4) [@@inline]
  let make5 k1 v1 k2 v2 k3 v3 k4 v4 k5 v5 =
    BR (2, make2 k1 v1 k2 v2, k3, v3, make2 k4 v4 k5 v5) [@@inline]

  let height = function
    | T0 -> 0
    | T1 _ | T2 _ | T3 _ | T4 _ -> 1
    | BR (h, _, _, _, _) -> h
  [@@inline]

  let rec length = function
    | T0 -> 0
    | T1 _ -> 1
    | T2 _ -> 2
    | T3 _ -> 3
    | T4 _ -> 4
    | BR (_, l, _, _, r) -> length l + 1 + length r

  let rec fold_kv x ~init ~f = match x with
    | T0 -> init
    | T1 (k, v) -> f init k v
    | T2 (k1, v1, k2, v2) -> f (f init k1 v1) k2 v2
    | T3 (k1, v1, k2, v2, k3, v3) -> f (f (f init k1 v1) k2 v2) k3 v3
    | T4 (k1, v1, k2, v2, k3, v3, k4, v4) ->
      f (f (f (f init k1 v1) k2 v2) k3 v3) k4 v4
    | BR (_, l, k, v, r) ->
      let init = fold_kv l ~init ~f in
      let init = f init k v in
      fold_kv r ~init ~f
  [@@specialise]

  let rec fold_kv_right x ~init ~f = match x with
    | T0 -> init
    | T1 (k, v) -> f k v init
    | T2 (k1, v1, k2, v2) -> f k1 v1 (f k2 v2 init)
    | T3 (k1, v1, k2, v2, k3, v3) -> f k1 v1 (f k2 v2 (f k3 v3 init))
    | T4 (k1, v1, k2, v2, k3, v3, k4, v4) ->
      f k1 v1 (f k2 v2 (f k3 v3 (f k4 v4 init)))
    | BR (_, l, k, v, r) ->
      let init = fold_kv_right r ~init ~f in
      let init = f k v init in
      fold_kv_right l ~init ~f
  [@@specialise]

  let[@tail_mod_cons] rec map_tree t ~f = match t with
    | T0 -> T0
    | T1 (k, v) -> T1 (k, f v)
    | T2 (k1, v1, k2, v2) -> T2 (k1, f v1, k2, f v2)
    | T3 (k1, v1, k2, v2, k3, v3) -> T3 (k1, f v1, k2, f v2, k3, f v3)
    | T4 (k1, v1, k2, v2, k3, v3, k4, v4) ->
      T4 (k1, f v1, k2, f v2, k3, f v3, k4, f v4)
    | BR (h, l, k, v, r) ->
      BR (h, map_tree l ~f, k, f v, (map_tree[@tailcall]) r ~f)

  (* Build a node from balanced subtrees `l` and `r` with:

     `all of l < k < all of r`, assuming `|height l - height r| <= 1`.

     When both sides are leaves numbering at most five with the pivot,
     collapse into a fat leaf, in place, with no intermediate list. This
     keeps the "at most four elements is a leaf" invariant and guarantees
     no `BR` ever holds a `T0` child.
  *)
  let create l k v r = match l, r with
    | T0, T0 -> make1 k v
    | T0, T1 (ka, va) -> make2 k v ka va
    | T0, T2 (ka, va, kb, vb) -> make3 k v ka va kb vb
    | T0, T3 (ka, va, kb, vb, kc, vc) -> make4 k v ka va kb vb kc vc
    | T0, T4 (ka, va, kb, vb, kc, vc, kd, vd) ->
      make5 k v ka va kb vb kc vc kd vd
    | T1 (ka, va), T0 -> make2 ka va k v
    | T1 (ka, va), T1 (kb, vb) -> make3 ka va k v kb vb
    | T1 (ka, va), T2 (kb, vb, kc, vc) -> make4 ka va k v kb vb kc vc
    | T1 (ka, va), T3 (kb, vb, kc, vc, kd, vd) ->
      make5 ka va k v kb vb kc vc kd vd
    | T2 (ka, va, kb, vb), T0 -> make3 ka va kb vb k v
    | T2 (ka, va, kb, vb), T1 (kc, vc) -> make4 ka va kb vb k v kc vc
    | T2 (ka, va, kb, vb), T2 (kc, vc, kd, vd) ->
      make5 ka va kb vb k v kc vc kd vd
    | T3 (ka, va, kb, vb, kc, vc), T0 -> make4 ka va kb vb kc vc k v
    | T3 (ka, va, kb, vb, kc, vc), T1 (kd, vd) ->
      make5 ka va kb vb kc vc k v kd vd
    | T4 (ka, va, kb, vb, kc, vc, kd, vd), T0 ->
      make5 ka va kb vb kc vc kd vd k v
    | (T1 _ | T2 _ | T3 _ | T4 _), (T1 _ | T2 _ | T3 _ | T4 _) ->
      BR (2, l, k, v, r)
    | _ -> BR (1 + Int.max (height l) (height r), l, k, v, r)

  let bal l k v r =
    let hl = height l and hr = height r in
    if hl > hr + 1 then
      match l with
      | BR (_, ll, lk, lv, lr) ->
        if height ll >= height lr
        then create ll lk lv (create lr k v r)
        else begin match lr with
          | BR (_, lrl, lrk, lrv, lrr) ->
            create (create ll lk lv lrl) lrk lrv (create lrr k v r)
          | _ -> assert false
        end
      | _ -> assert false
    else if hr > hl + 1 then
      match r with
      | BR (_, rl, rk, rv, rr) ->
        if height rr >= height rl
        then create (create l k v rl) rk rv rr
        else begin match rl with
          | BR (_, rll, rlk, rlv, rlr) ->
            create (create l k v rll) rlk rlv (create rlr rk rv rr)
          | _ -> assert false
        end
      | _ -> assert false
    else create l k v r

  let rec upsert q ~has ~nil t = match t with
    | T0 -> make1 q (nil ())
    | T1 (kb, b) ->
      let c = Key.compare q kb in
      if c = 0 then make1 q (has b)
      else if c < 0 then make2 q (nil ()) kb b
      else make2 kb b q (nil ())
    | T2 (kb, b, kc, c) ->
      let c1 = Key.compare q kb in
      if c1 = 0 then make2 q (has b) kc c
      else if c1 < 0 then make3 q (nil ()) kb b kc c
      else
        let c2 = Key.compare q kc in
        if c2 = 0 then make2 kb b q (has c)
        else if c2 < 0 then make3 kb b q (nil ()) kc c
        else make3 kb b kc c q (nil ())
    | T3 (kb, b, kc, c, kd, d) ->
      let cc = Key.compare q kc in
      if cc = 0 then make3 kb b q (has c) kd d
      else if cc < 0 then
        let cb = Key.compare q kb in
        if cb = 0 then make3 q (has b) kc c kd d
        else if cb < 0 then make4 q (nil ()) kb b kc c kd d
        else make4 kb b q (nil ()) kc c kd d
      else
        let cd = Key.compare q kd in
        if cd = 0 then make3 kb b kc c q (has d)
        else if cd < 0 then make4 kb b kc c q (nil ()) kd d
        else make4 kb b kc c kd d q (nil ())
    | T4 (kb, b, kc, c, kd, d, ke, e) ->
      let cd = Key.compare q kd in
      if cd = 0 then make4 kb b kc c q (has d) ke e
      else if cd > 0 then
        let ce = Key.compare q ke in
        if ce = 0 then make4 kb b kc c kd d q (has e)
        else if ce < 0 then make5 kb b kc c kd d q (nil ()) ke e
        else make5 kb b kc c kd d ke e q (nil ())
      else
        let cc = Key.compare q kc in
        if cc = 0 then make4 kb b q (has c) kd d ke e
        else if cc > 0 then make5 kb b kc c q (nil ()) kd d ke e
        else
          let cb = Key.compare q kb in
          if cb = 0 then make4 q (has b) kc c kd d ke e
          else if cb < 0 then make5 q (nil ()) kb b kc c kd d ke e
          else make5 kb b q (nil ()) kc c kd d ke e
    | BR (h, l, pk, pv, r) ->
      let c = Key.compare q pk in
      if c = 0 then BR (h, l, q, has pv, r)
      else if c < 0 then bal (upsert q ~has ~nil l) pk pv r
      else bal l pk pv (upsert q ~has ~nil r)

  let rec find_tree q = function
    | T0 -> None
    | T1 (ka, a) -> if Key.compare q ka = 0 then Some a else None
    | T2 (ka, a, kb, b) ->
      begin match Key.compare q kb with
        | 0 -> Some b
        | n when n > 0 -> None
        | _ -> if Key.compare q ka = 0 then Some a else None
      end
    | T3 (ka, a, kb, b, kc, c) ->
      begin match Key.compare q kb with
        | 0 -> Some b
        | n when n > 0 -> if Key.compare q kc = 0 then Some c else None
        | _ -> if Key.compare q ka = 0 then Some a else None
      end
    | T4 (ka, a, kb, b, kc, c, kd, d) ->
      begin match Key.compare q kc with
        | 0 -> Some c
        | n when n > 0 -> if Key.compare q kd = 0 then Some d else None
        | _ -> match Key.compare q kb with
          | 0 -> Some b
          | n when n > 0 -> None
          | _ -> if Key.compare q ka = 0 then Some a else None
      end
    | BR (_, l, pk, pv, r) ->
      begin match Key.compare q pk with
        | 0 -> Some pv
        | n when n > 0 -> find_tree q r
        | _ -> find_tree q l
      end

  let rec remove_min = function
    | T0 -> assert false
    | T1 (k, v) -> k, v, T0
    | T2 (k1, v1, k2, v2) -> k1, v1, make1 k2 v2
    | T3 (k1, v1, k2, v2, k3, v3) -> k1, v1, make2 k2 v2 k3 v3
    | T4 (k1, v1, k2, v2, k3, v3, k4, v4) -> k1, v1, make3 k2 v2 k3 v3 k4 v4
    | BR (_, l, k, v, r) ->
      let k', v', l' = remove_min l in
      k', v', bal l' k v r

  let merge_subtrees l r = match l, r with
    | T0, t | t, T0 -> t
    | _ ->
      let k, v, r' = remove_min r in
      bal l k v r'
  [@@inline]

  let rec remove_tree q t = match t with
    | T0 -> T0
    | T1 (kb, _) -> if Key.compare q kb = 0 then T0 else t
    | T2 (kb, b, kc, c) ->
      let c1 = Key.compare q kb in
      if c1 = 0 then make1 kc c
      else if c1 < 0 then t
      else if Key.compare q kc = 0 then make1 kb b
      else t
    | T3 (kb, b, kc, c, kd, d) ->
      let cc = Key.compare q kc in
      if cc = 0 then make2 kb b kd d
      else if cc < 0 then
        if Key.compare q kb = 0 then make2 kc c kd d else t
      else (if Key.compare q kd = 0 then make2 kb b kc c else t)
    | T4 (kb, b, kc, c, kd, d, ke, e) ->
      let cd = Key.compare q kd in
      if cd = 0 then make3 kb b kc c ke e
      else if cd > 0 then
        if Key.compare q ke = 0 then make3 kb b kc c kd d else t
      else
        let cc = Key.compare q kc in
        if cc = 0 then make3 kb b kd d ke e
        else if cc < 0 then
          if Key.compare q kb = 0 then make3 kc c kd d ke e else t
        else t
    | BR (_, l, pk, pv, r) ->
      begin match Key.compare q pk with
        | 0 -> merge_subtrees l r
        | n when n < 0 -> bal (remove_tree q l) pk pv r
        | _ -> bal l pk pv (remove_tree q r)
      end

  let fold_merge ~f x y =
    fold_kv y ~init:x ~f:(fun x ky vy ->
        upsert ky x
          ~has:(fun vx -> f ~key:ky vx vy)
          ~nil:(fun () -> vy))

  let merge_11 ~f ka a kb b = match Key.compare ka kb with
    | 0 -> make1 ka (f ~key:ka a b)
    | n when n > 0 -> make2 kb b ka a
    | _ -> make2 ka a kb b

  let merge_12 ~f ka a kb b kc c = match AP.relate ka (kb, kc) with
    | Before   -> make3 ka a kb b kc c
    | Starts   -> make2 ka (f ~key:ka a b) kc c
    | During   -> make3 kb b ka a kc c
    | Finishes -> make2 kb b ka (f ~key:ka a c)
    | After    -> make3 kb b kc c ka a

  let merge_21 ~f kb b kc c ka a = match AP.relate ka (kb, kc) with
    | Before   -> make3 ka a kb b kc c
    | Starts   -> make2 kb (f ~key:kb b a) kc c
    | During   -> make3 kb b ka a kc c
    | Finishes -> make2 kb b kc (f ~key:kc c a)
    | After    -> make3 kb b kc c ka a

  let merge_13 ~f ka a kb b kc c kd d = match AP.relate ka (kb, kd) with
    | Before   -> make4 ka a kb b kc c kd d
    | Starts   -> make3 ka (f ~key:ka a b) kc c kd d
    | Finishes -> make3 kb b kc c kd (f ~key:kd a d)
    | After    -> make4 kb b kc c kd d ka a
    | During   -> match Key.compare ka kc with
      | 0            -> make3 kb b kc (f ~key:kc a c) kd d
      | n when n > 0 -> make4 kb b kc c ka a kd d
      | _            -> make4 kb b ka a kc c kd d

  let merge_31 ~f kb b kc c kd d ka a = match AP.relate ka (kb, kd) with
    | Before   -> make4 ka a kb b kc c kd d
    | Starts   -> make3 kb (f ~key:kb b a) kc c kd d
    | Finishes -> make3 kb b kc c kd (f ~key:kd d a)
    | After    -> make4 kb b kc c kd d ka a
    | During   -> match Key.compare ka kc with
      | 0            -> make3 kb b kc (f ~key:kc c a) kd d
      | n when n > 0 -> make4 kb b kc c ka a kd d
      | _            -> make4 kb b ka a kc c kd d

  let merge_22 ~f ka a kb b kc c kd d = match AI.relate (ka, kb) (kc, kd) with
    | Meets         -> make3 ka a kb (f ~key:kb b c) kd d
    | Met_by        -> make3 kc c kd (f ~key:kd a d) kb b
    | Before        -> make4 ka a kb b kc c kd d
    | After         -> make4 kc c kd d ka a kb b
    | Overlaps      -> make4 ka a kc c kb b kd d
    | Overlapped_by -> make4 kc c ka a kd d kb b
    | Starts        -> make3 ka (f ~key:ka a c) kb b kd d
    | Started_by    -> make3 ka (f ~key:ka a c) kd d kb b
    | Finishes      -> make3 kc c ka a kb (f ~key:kb b d)
    | Finished_by   -> make3 ka a kc c kb (f ~key:kb b d)
    | During        -> make4 kc c ka a kb b kd d
    | Contains      -> make4 ka a kc c kd d kb b
    | Equal         -> make2 ka (f ~key:ka a c) kb (f ~key:kb b d)

  let merge_tree ~f x y =
    if phys_equal x y then x
    else match x, y with
      | T0, x | x, T0 -> x
      | T1 (ka, a), T1 (kb, b) -> merge_11 ~f ka a kb b
      | T1 (ka, a), T2 (kb, b, kc, c) -> merge_12 ~f ka a kb b kc c
      | T2 (kb, b, kc, c), T1 (ka, a) -> merge_21 ~f kb b kc c ka a
      | T1 (ka, a), T3 (kb, b, kc, c, kd, d) -> merge_13 ~f ka a kb b kc c kd d
      | T3 (kb, b, kc, c, kd, d), T1 (ka, a) -> merge_31 ~f kb b kc c kd d ka a
      | T2 (ka, a, kb, b), T2 (kc, c, kd, d) -> merge_22 ~f ka a kb b kc c kd d
      | _ -> fold_merge ~f x y

  let to_seq =
    let open Sequence.Generator in
    let rec aux = function
      | T0 -> return ()
      | T1 (k, v) -> yield (k, v)
      | T2 (k1, v1, k2, v2) ->
        yield (k1, v1) >>= fun () ->
        yield (k2, v2)
      | T3 (k1, v1, k2, v2, k3, v3) ->
        yield (k1, v1) >>= fun () ->
        yield (k2, v2) >>= fun () ->
        yield (k3, v3)
      | T4 (k1, v1, k2, v2, k3, v3, k4, v4) ->
        yield (k1, v1) >>= fun () ->
        yield (k2, v2) >>= fun () ->
        yield (k3, v3) >>= fun () ->
        yield (k4, v4)
      | BR (_, l, k, v, r) ->
        aux l >>= fun () ->
        yield (k, v) >>= fun () ->
        aux r in
    fun t -> run (aux t)

  let to_seq_rev =
    let open Sequence.Generator in
    let rec aux = function
      | T0 -> return ()
      | T1 (k, v) -> yield (k, v)
      | T2 (k1, v1, k2, v2) ->
        yield (k2, v2) >>= fun () ->
        yield (k1, v1)
      | T3 (k1, v1, k2, v2, k3, v3) ->
        yield (k3, v3) >>= fun () ->
        yield (k2, v2) >>= fun () ->
        yield (k1, v1)
      | T4 (k1, v1, k2, v2, k3, v3, k4, v4) ->
        yield (k4, v4) >>= fun () ->
        yield (k3, v3) >>= fun () ->
        yield (k2, v2) >>= fun () ->
        yield (k1, v1)
      | BR (_, l, k, v, r) ->
        aux r >>= fun () ->
        yield (k, v) >>= fun () ->
        aux l in
    fun t -> run (aux t)

  let fold t ~init ~f = fold_kv t ~init ~f:(fun acc _ v -> f acc v) [@@inline]

  let fold_right t ~init ~f =
    fold_kv_right t ~init ~f:(fun _ v acc -> f v acc) [@@inline]

  let foldi t ~init ~f =
    fold_kv t ~init ~f:(fun acc key data -> f ~key ~data acc) [@@inline]

  let foldi_right t ~init ~f =
    fold_kv_right t ~init ~f:(fun key data acc -> f ~key ~data acc) [@@inline]

  let iter t ~f = fold_kv t ~init:() ~f:(fun () _ v -> f v) [@@inline]

  let iteri t ~f =
    fold_kv t ~init:() ~f:(fun () key data -> f ~key ~data) [@@inline]

  let map t ~f = map_tree t ~f

  let set t ~key ~data =
    upsert key t ~has:(fun _ -> data) ~nil:(fun () -> data)

  let remove t key = remove_tree key t

  let update t key ~f =
    upsert key t ~has:(fun old -> f (Some old)) ~nil:(fun () -> f None)

  let update_with t key ~has ~nil = upsert key t ~has ~nil

  let add_exn t ~key ~data =
    upsert key t ~has:(fun _ -> raise Duplicate) ~nil:(fun () -> data)

  let add t ~key ~data =
    try `Ok (add_exn t ~key ~data) with Duplicate -> `Duplicate

  let find t key = find_tree key t

  let find_exn t key = match find t key with
    | Some v -> v
    | None -> raise Not_found

  let mem t key = Option.is_some (find_tree key t)

  let merge t1 t2 ~f = merge_tree ~f t1 t2

  let to_list t = fold_kv_right t ~init:[] ~f:(fun k v acc -> (k, v) :: acc)
  let to_list_rev t = fold_kv t ~init:[] ~f:(fun acc k v -> (k, v) :: acc)
  let keys t = fold_kv_right t ~init:[] ~f:(fun k _ acc -> k :: acc)
  let data t = fold_kv_right t ~init:[] ~f:(fun _ v acc -> v :: acc)

  let of_alist_exn l =
    List.fold l ~init:empty ~f:(fun acc (key, data) -> add_exn acc ~key ~data)

  let of_alist l =
    try `Ok (of_alist_exn l) with Duplicate -> `Duplicate

  let to_sequence t = to_seq t
  let to_sequence_rev t = to_seq_rev t

  let compare compare_a t1 t2 =
    Sequence.compare
      (fun (k1, v1) (k2, v2) -> match Key.compare k1 k2 with
         | 0 -> compare_a v1 v2
         | c -> c)
      (to_seq t1) (to_seq t2)

  let equal equal_a t1 t2 =
    Sequence.equal
      (fun (k1, v1) (k2, v2) ->
         Key.equal k1 k2 && equal_a v1 v2)
      (to_seq t1) (to_seq t2)

  let sexp_of_t sexp_of_a t =
    Sexp.List (
      fold_kv_right t ~init:[]
        ~f:(fun k v acc ->
            Sexp.List [
              Key.sexp_of_t k;
              sexp_of_a v;
            ] :: acc))

  let t_of_sexp a_of_sexp = function
    | Sexp.List items ->
      List.fold items ~init:empty ~f:(fun acc -> function
          | Sexp.List [ks; vs] ->
            set acc ~key:(Key.t_of_sexp ks) ~data:(a_of_sexp vs)
          | other ->
            Sexplib0.Sexp_conv.of_sexp_error
              "Small_map.t_of_sexp: expected a (key value) pair" other)
    | other ->
      Sexplib0.Sexp_conv.of_sexp_error
        "Small_map.t_of_sexp: expected a list" other
end
