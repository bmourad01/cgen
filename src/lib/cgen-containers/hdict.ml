(** A type-safe, heterogeneous dictionary.

    We implement as a height-balanced (AVL) tree with fat leaves, keyed by each
    key's [uid]. The key and value of each slot are stored inline as an
    existentially-packed pair directly in the GADT constructors (no separate
    binding box).

    The leaf shape and heterogeneous-key discipline are adapted from BAP's
    Knowledge Base, while the internal nodes ([BR]) are a standard AVL with the
    height stored in the node.

    This mirrors {!Small_map}'s balancing exactly. It is duplicated rather than
    shared so that both keep their leanest representation (the monomorphic map
    inlines a plain key, the dictionary inlines an existential key).
*)

open Core

module type Name = Hdict_intf.Name

module Make(Name : Name) : sig
  module Key : Hdict_intf.Key
    with type name := Name.t
     and type uid := int

  include Hdict_intf.S with type 'a key = 'a Key.t
end = struct
  module Key = Hdict_key.Make(Name)

  type 'a key = 'a Key.t

  type t =
    | T0
    | T1 : 'a key * 'a -> t
    | T2 : 'a key * 'a * 'b key * 'b -> t
    | T3 : 'a key * 'a * 'b key * 'b * 'c key * 'c -> t
    | T4 : 'a key * 'a * 'b key * 'b * 'c key * 'c * 'd key * 'd -> t
    | BR : int * t * 'a key * 'a * t -> t
    (* height, left, pivot-key, pivot-value, right *)

  exception Not_found
  exception Duplicate

  type 'r visitor = {
    visit : 'a. 'a key -> 'a -> 'r -> 'r;
  }

  type merge = {
    merge : 'a. 'a key -> 'a -> 'a -> 'a;
  }

  (* Recover the value type when two keys share a uid. *)
  let coerce : type a b. a key -> b key -> b -> a =
    fun q k v -> match Key.same q k with Type_equal.T -> v
  [@@inline]

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

  let rec foreach : type r. t -> init:r -> r visitor -> r = fun t ~init v ->
    match t with
    | T0 -> init
    | T1 (k, x) -> v.visit k x init
    | T2 (k1, x1, k2, x2) -> v.visit k2 x2 (v.visit k1 x1 init)
    | T3 (k1, x1, k2, x2, k3, x3) ->
      v.visit k3 x3 (v.visit k2 x2 (v.visit k1 x1 init))
    | T4 (k1, x1, k2, x2, k3, x3, k4, x4) ->
      v.visit k4 x4 (v.visit k3 x3 (v.visit k2 x2 (v.visit k1 x1 init)))
    | BR (_, l, k, x, r) ->
      foreach r ~init:(v.visit k x (foreach l ~init v)) v

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

  let rec insert : type a. a key -> a -> t -> t = fun ka a t -> match t with
    | T0 -> make1 ka a
    | T1 (kb, b) ->
      if Key.compare ka kb < 0 then make2 ka a kb b else make2 kb b ka a
    | T2 (kb, b, kc, c) ->
      if Key.compare ka kb < 0 then make3 ka a kb b kc c
      else if Key.compare ka kc < 0 then make3 kb b ka a kc c
      else make3 kb b kc c ka a
    | T3 (kb, b, kc, c, kd, d) ->
      if Key.compare ka kc < 0 then
        if Key.compare ka kb < 0 then make4 ka a kb b kc c kd d
        else make4 kb b ka a kc c kd d
      else if Key.compare ka kd < 0 then make4 kb b kc c ka a kd d
      else make4 kb b kc c kd d ka a
    | T4 (kb, b, kc, c, kd, d, ke, e) ->
      if Key.compare ka kd < 0 then
        if Key.compare ka kc < 0 then
          if Key.compare ka kb < 0 then make5 ka a kb b kc c kd d ke e
          else make5 kb b ka a kc c kd d ke e
        else make5 kb b kc c ka a kd d ke e
      else if Key.compare ka ke < 0 then make5 kb b kc c kd d ka a ke e
      else make5 kb b kc c kd d ke e ka a
    | BR (_, l, k, v, r) ->
      if Key.compare ka k < 0
      then bal (insert ka a l) k v r
      else bal l k v (insert ka a r)

  let rec upsert : type a. a key -> has:(a -> a) -> nil:(unit -> a) -> t -> t =
    fun q ~has ~nil t -> match t with
      | T0 -> make1 q (nil ())
      | T1 (kb, b) ->
        let c = Key.compare q kb in
        if c = 0 then make1 q (has (coerce q kb b))
        else if c < 0 then make2 q (nil ()) kb b
        else make2 kb b q (nil ())
      | T2 (kb, b, kc, c) ->
        let c1 = Key.compare q kb in
        if c1 = 0 then make2 q (has (coerce q kb b)) kc c
        else if c1 < 0 then make3 q (nil ()) kb b kc c
        else
          let c2 = Key.compare q kc in
          if c2 = 0 then make2 kb b q (has (coerce q kc c))
          else if c2 < 0 then make3 kb b q (nil ()) kc c
          else make3 kb b kc c q (nil ())
      | T3 (kb, b, kc, c, kd, d) ->
        let cc = Key.compare q kc in
        if cc = 0 then make3 kb b q (has (coerce q kc c)) kd d
        else if cc < 0 then
          let cb = Key.compare q kb in
          if cb = 0 then make3 q (has (coerce q kb b)) kc c kd d
          else if cb < 0 then make4 q (nil ()) kb b kc c kd d
          else make4 kb b q (nil ()) kc c kd d
        else
          let cd = Key.compare q kd in
          if cd = 0 then make3 kb b kc c q (has (coerce q kd d))
          else if cd < 0 then make4 kb b kc c q (nil ()) kd d
          else make4 kb b kc c kd d q (nil ())
      | T4 (kb, b, kc, c, kd, d, ke, e) ->
        let cd = Key.compare q kd in
        if cd = 0 then make4 kb b kc c q (has (coerce q kd d)) ke e
        else if cd > 0 then
          let ce = Key.compare q ke in
          if ce = 0 then make4 kb b kc c kd d q (has (coerce q ke e))
          else if ce < 0 then make5 kb b kc c kd d q (nil ()) ke e
          else make5 kb b kc c kd d ke e q (nil ())
        else
          let cc = Key.compare q kc in
          if cc = 0 then make4 kb b q (has (coerce q kc c)) kd d ke e
          else if cc > 0 then make5 kb b kc c q (nil ()) kd d ke e
          else
            let cb = Key.compare q kb in
            if cb = 0 then make4 q (has (coerce q kb b)) kc c kd d ke e
            else if cb < 0 then make5 q (nil ()) kb b kc c kd d ke e
            else make5 kb b q (nil ()) kc c kd d ke e
      | BR (h, l, pk, pv, r) ->
        let c = Key.compare q pk in
        if c = 0 then BR (h, l, q, has (coerce q pk pv), r)
        else if c < 0 then bal (upsert q ~has ~nil l) pk pv r
        else bal l pk pv (upsert q ~has ~nil r)

  let rec find : type a. a key -> t -> a option = fun q t -> match t with
    | T0 -> None
    | T1 (ka, a) -> if Key.compare q ka = 0 then Some (coerce q ka a) else None
    | T2 (ka, a, kb, b) ->
      begin match Key.compare q kb with
        | 0 -> Some (coerce q kb b)
        | n when n > 0 -> None
        | _ -> if Key.compare q ka = 0 then Some (coerce q ka a) else None
      end
    | T3 (ka, a, kb, b, kc, c) ->
      begin match Key.compare q kb with
        | 0 -> Some (coerce q kb b)
        | n when n > 0 -> if Key.compare q kc = 0 then Some (coerce q kc c) else None
        | _ -> if Key.compare q ka = 0 then Some (coerce q ka a) else None
      end
    | T4 (ka, a, kb, b, kc, c, kd, d) ->
      begin match Key.compare q kc with
        | 0 -> Some (coerce q kc c)
        | n when n > 0 -> if Key.compare q kd = 0 then Some (coerce q kd d) else None
        | _ -> match Key.compare q kb with
          | 0 -> Some (coerce q kb b)
          | n when n > 0 -> None
          | _ -> if Key.compare q ka = 0 then Some (coerce q ka a) else None
      end
    | BR (_, l, pk, pv, r) ->
      begin match Key.compare q pk with
        | 0 -> Some (coerce q pk pv)
        | n when n > 0 -> find q r
        | _ -> find q l
      end

  let get q t = match find q t with
    | Some v -> v
    | None -> raise Not_found

  let mem q t = Option.is_some (find q t) [@@inline]

  (* The plucked minimum is existentially typed, so it is delivered to a
     polymorphic continuation rather than returned in a tuple. *)
  type 'r min_kont = {
    min : 'a. 'a key -> 'a -> t -> 'r;
  }

  let rec remove_min : type r. t -> r min_kont -> r = fun t k -> match t with
    | T0 -> assert false
    | T1 (ka, a) -> k.min ka a T0
    | T2 (ka, a, kb, b) -> k.min ka a (make1 kb b)
    | T3 (ka, a, kb, b, kc, c) -> k.min ka a (make2 kb b kc c)
    | T4 (ka, a, kb, b, kc, c, kd, d) -> k.min ka a (make3 kb b kc c kd d)
    | BR (_, l, kp, vp, r) ->
      remove_min l {
        min = fun kmin vmin l' ->
          k.min kmin vmin (bal l' kp vp r);
      }

  let merge_subtrees l r = match l, r with
    | T0, t | t, T0 -> t
    | _ ->
      remove_min r {
        min = fun kmin vmin r' -> bal l kmin vmin r';
      }

  let rec remove : type a. a key -> t -> t = fun q t -> match t with
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
      else if Key.compare q kd = 0 then make2 kb b kc c else t
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
        | n when n < 0 -> bal (remove q l) pk pv r
        | _ -> bal l pk pv (remove q r)
      end

  let set k v t = upsert k ~has:(fun _ -> v) ~nil:(fun () -> v) t

  let update (f : 'a -> 'a -> 'a) (k : 'a key) (v : 'a) t =
    upsert k ~has:(fun old -> f old v) ~nil:(fun () -> v) t

  let add k v t =
    try `Ok (upsert k ~has:(fun _ -> raise Duplicate) ~nil:(fun () -> v) t)
    with Duplicate -> `Duplicate

  let change k t ~f = match f (find k t) with
    | Some v -> set k v t
    | None -> remove k t

  module KI = struct
    type point = int
    type t = point * point
    let lo = fst
    let hi = snd
    let (<)  = Int.(<)
    let (>)  = Int.(>)
    let (<=) = Int.(<=)
    let (>=) = Int.(>=)
    let (=)  = Int.(=)
    let (<>) = Int.(<>)
  end

  module AP = Cgen_utils.Allen_point_algebra.Make(KI)
  module AI = Cgen_utils.Allen_interval_algebra.Make(KI)

  let pk k = Key.uid k [@@inline]
  let ik a b = Key.uid a, Key.uid b [@@inline]

  (* Merge two slots proven to share a uid.

     - `mL` types the result as the left key's value
     - `mR` as the right key's value
     - both pass `m.merge k xv yv` with the `x`-side value first

     This fulfills the contract for `merge`, in that it is right-side biased.
  *)

  let mL : type a b. merge -> a key -> a -> b key -> b -> a =
    fun m ka a kb b -> m.merge ka a (coerce ka kb b)

  let mR : type a b. merge -> a key -> a -> b key -> b -> b =
    fun m ka a kb b -> m.merge kb (coerce kb ka a) b

  let fold_merge (m : merge) x y =
    foreach y ~init:x {
      visit = fun ky vy acc ->
        upsert ky acc
          ~has:(fun vx -> m.merge ky vx vy)
          ~nil:(fun () -> vy)
    }

  let merge_11 m ka a kb b = match Key.compare ka kb with
    | 0 -> make1 ka (mL m ka a kb b)
    | n when n > 0 -> make2 kb b ka a
    | _ -> make2 ka a kb b

  let merge_12 m ka a kb b kc c = match AP.relate (pk ka) (ik kb kc) with
    | Before   -> make3 ka a kb b kc c
    | Starts   -> make2 ka (mL m ka a kb b) kc c
    | During   -> make3 kb b ka a kc c
    | Finishes -> make2 kb b ka (mL m ka a kc c)
    | After    -> make3 kb b kc c ka a

  let merge_21 m kb b kc c ka a = match AP.relate (pk ka) (ik kb kc) with
    | Before   -> make3 ka a kb b kc c
    | Starts   -> make2 kb (mL m kb b ka a) kc c
    | During   -> make3 kb b ka a kc c
    | Finishes -> make2 kb b kc (mL m kc c ka a)
    | After    -> make3 kb b kc c ka a

  let merge_13 m ka a kb b kc c kd d = match AP.relate (pk ka) (ik kb kd) with
    | Before   -> make4 ka a kb b kc c kd d
    | Starts   -> make3 ka (mL m ka a kb b) kc c kd d
    | Finishes -> make3 kb b kc c kd (mR m ka a kd d)
    | After    -> make4 kb b kc c kd d ka a
    | During   -> match Key.compare ka kc with
      | 0            -> make3 kb b kc (mR m ka a kc c) kd d
      | n when n > 0 -> make4 kb b kc c ka a kd d
      | _            -> make4 kb b ka a kc c kd d

  let merge_31 m kb b kc c kd d ka a = match AP.relate (pk ka) (ik kb kd) with
    | Before   -> make4 ka a kb b kc c kd d
    | Starts   -> make3 kb (mL m kb b ka a) kc c kd d
    | Finishes -> make3 kb b kc c kd (mL m kd d ka a)
    | After    -> make4 kb b kc c kd d ka a
    | During   -> match Key.compare ka kc with
      | 0            -> make3 kb b kc (mL m kc c ka a) kd d
      | n when n > 0 -> make4 kb b kc c ka a kd d
      | _            -> make4 kb b ka a kc c kd d

  let merge_22 m ka a kb b kc c kd d = match AI.relate (ik ka kb) (ik kc kd) with
    | Meets         -> make3 ka a kb (mL m kb b kc c) kd d
    | Met_by        -> make3 kc c kd (mR m ka a kd d) kb b
    | Before        -> make4 ka a kb b kc c kd d
    | After         -> make4 kc c kd d ka a kb b
    | Overlaps      -> make4 ka a kc c kb b kd d
    | Overlapped_by -> make4 kc c ka a kd d kb b
    | Starts        -> make3 ka (mL m ka a kc c) kb b kd d
    | Started_by    -> make3 ka (mL m ka a kc c) kd d kb b
    | Finishes      -> make3 kc c ka a kb (mL m kb b kd d)
    | Finished_by   -> make3 ka a kc c kb (mL m kb b kd d)
    | During        -> make4 kc c ka a kb b kd d
    | Contains      -> make4 ka a kc c kd d kb b
    | Equal         -> make2 ka (mL m ka a kc c) kb (mL m kb b kd d)

  let merge (m : merge) x y =
    if phys_equal x y then x
    else match x, y with
      | T0, x | x, T0 -> x
      | T1 (ka, a), T1 (kb, b) -> merge_11 m ka a kb b
      | T1 (ka, a), T2 (kb, b, kc, c) -> merge_12 m ka a kb b kc c
      | T2 (kb, b, kc, c), T1 (ka, a) -> merge_21 m kb b kc c ka a
      | T1 (ka, a), T3 (kb, b, kc, c, kd, d) -> merge_13 m ka a kb b kc c kd d
      | T3 (kb, b, kc, c, kd, d), T1 (ka, a) -> merge_31 m kb b kc c kd d ka a
      | T2 (ka, a, kb, b), T2 (kc, c, kd, d) -> merge_22 m ka a kb b kc c kd d
      | _ -> fold_merge m x y

  let sexp_of_t t =
    Sexp.List (List.rev (foreach t ~init:[] {
        visit = fun k x acc ->
          Sexp.List [Sexp.Atom (Name.to_string (Key.name k)); Key.to_sexp k x]
          :: acc
      }))

  let pp_key ppf k = Format.fprintf ppf "%s" (Name.to_string (Key.name k))

  let pp ppf t =
    Format.fprintf ppf "{@[<2>@,";
    ignore (foreach t ~init:true {
        visit = fun k x first ->
          if not first then Format.fprintf ppf ";@ ";
          Format.fprintf ppf "%s : %a"
            (Name.to_string (Key.name k)) Sexp.pp_hum (Key.to_sexp k x);
          false
      });
    Format.fprintf ppf "@]}"

  module Internal = struct
    let is_rank1 = function
      | T1 _ | T2 _ | T3 _ | T4 _ -> true
      | _ -> false

    let insert k v t = insert k v t
  end
end
