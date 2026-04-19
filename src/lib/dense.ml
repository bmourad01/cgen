open Core
open Dense_intf

module OA = Option_array

let (.![]) = Array.unsafe_get
let (.![]<-) = Array.unsafe_set
let (.?[]) = OA.unsafe_get_some_assuming_some
let (.?[]<-) = OA.unsafe_set_some

let initial_capacity = 8

let probe_of ~to_int mask key idx =
  let preferred = to_int key land mask in
  let distance = idx - preferred in
  (distance + mask + 1) land mask
[@@inline] [@@specialise]

let find_slot ~to_int ~equal ~empty_sentinel mask keys key =
  let idx = ref (to_int key land mask) in
  let continue = ref true in
  let result = ref (-1) in
  let distance = ref 0 in
  while !continue do
    let k = keys.![!idx] in
    match () with
    | () when equal k empty_sentinel ->
      continue := false
    | () when equal k key ->
      result := !idx;
      continue := false
    | () when probe_of ~to_int mask k !idx < !distance ->
      continue := false
    | () ->
      idx := (!idx + 1) land mask;
      incr distance
  done;
  !result
[@@inline] [@@specialise]

module Make_map(K : Key) : Map with type key = K.t = struct
  type key = K.t

  type 'a t = {
    mutable keys   : K.t array;
    mutable vals   : 'a OA.t;
    mutable length : int;
    mutable mask   : int;
  }

  exception Duplicate
  exception Not_found

  let create ?(capacity = initial_capacity) () =
    let cap = Int.(ceil_pow2 @@ max capacity initial_capacity) in {
      keys = Array.create ~len:cap K.empty_sentinel;
      vals = OA.create ~len:cap;
      length = 0;
      mask = cap - 1;
    }

  let clear t =
    Array.fill t.keys ~pos:0 ~len:(Array.length t.keys) K.empty_sentinel;
    OA.clear t.vals;
    t.length <- 0

  let length t = t.length
  let is_empty t = t.length = 0

  let probe_of mask key idx =
    let open K in
    probe_of ~to_int mask key idx
  [@@inline]

  let find_slot t key =
    let open K in
    find_slot ~to_int ~equal ~empty_sentinel t.mask t.keys key
  [@@inline]

  let mem t key = find_slot t key >= 0 [@@inline]

  let find t key =
    let i = find_slot t key in
    if i < 0 then None else OA.unsafe_get t.vals i
  [@@inline]

  let find_exn t key =
    let i = find_slot t key in
    if i < 0 then raise Not_found else t.vals.?[i]
  [@@inline]

  let insert_fresh t key data =
    let mask = t.mask in
    let keys = t.keys in
    let vals = t.vals in
    let cur_key = ref key in
    let cur_val = ref data in
    let idx = ref (K.to_int key land mask) in
    let distance = ref 0 in
    let continue = ref true in
    while !continue do
      let k = keys.![!idx] in
      match () with
      | () when K.equal k K.empty_sentinel ->
        keys.![!idx] <- !cur_key;
        vals.?[!idx] <- !cur_val;
        continue := false
      | () -> match probe_of mask k !idx with
        | distance' when distance' < !distance ->
          let old_val = vals.?[!idx] in
          keys.![!idx] <- !cur_key;
          vals.?[!idx] <- !cur_val;
          cur_key := k;
          cur_val := old_val;
          distance := distance' + 1;
          idx := (!idx + 1) land mask
        | _ ->
          incr distance;
          idx := (!idx + 1) land mask
    done

  let resize t =
    let old_keys = t.keys in
    let old_vals = t.vals in
    let new_cap = Array.length old_keys * 2 in
    t.keys <- Array.create ~len:new_cap K.empty_sentinel;
    t.vals <- OA.create ~len:new_cap;
    t.mask <- new_cap - 1;
    for i = 0 to Array.length old_keys - 1 do
      let k = old_keys.![i] in
      if not (K.equal k K.empty_sentinel) then
        insert_fresh t k old_vals.?[i]
    done

  (* Load factor 3/4 before resize. *)
  let grow_if_needed t =
    let cap = Array.length t.keys in
    if (t.length + 1) * 4 > cap * 3 then resize t
  [@@inline]

  let set t ~key ~data = match find_slot t key with
    | i when i < 0 ->
      grow_if_needed t;
      insert_fresh t key data;
      t.length <- t.length + 1
    | i -> t.vals.?[i] <- data

  let add_exn t ~key ~data =
    let i = find_slot t key in
    if i >= 0 then raise Duplicate;
    grow_if_needed t;
    insert_fresh t key data;
    t.length <- t.length + 1

  let find_or_add t key ~default =
    let i = find_slot t key in
    if i >= 0 then t.vals.?[i] else
      let data = default () in
      grow_if_needed t;
      insert_fresh t key data;
      t.length <- t.length + 1;
      data

  let update t key ~f =
    let i = find_slot t key in
    if i >= 0 then
      t.vals.?[i] <- f (OA.unsafe_get t.vals i)
    else
      let data = f None in
      grow_if_needed t;
      insert_fresh t key data;
      t.length <- t.length + 1

  let add_multi t ~key ~data = update t key ~f:(function
      | Some xs -> data :: xs
      | None -> [data])

  let shift_back t start =
    let mask = t.mask in
    let keys = t.keys in
    let vals = t.vals in
    let idx = ref start in
    let continue = ref true in
    while !continue do
      let j = (!idx + 1) land mask in
      let kj = keys.![j] in
      match () with
      | () when K.equal kj K.empty_sentinel ->
        keys.![!idx] <- K.empty_sentinel;
        continue := false
      | () when probe_of mask kj j = 0 ->
        keys.![!idx] <- K.empty_sentinel;
        continue := false
      | () ->
        keys.![!idx] <- kj;
        vals.?[!idx] <- vals.?[j];
        idx := j
    done

  let remove t key = match find_slot t key with
    | i when i >= 0 ->
      shift_back t i;
      t.length <- t.length - 1
    | _ -> ()

  let change t key ~f =
    let i = find_slot t key in
    if i >= 0 then match f @@ OA.unsafe_get t.vals i with
      | Some v -> t.vals.?[i] <- v
      | None ->
        shift_back t i;
        t.length <- t.length - 1
    else match f None with
      | None -> ()
      | Some v ->
        grow_if_needed t;
        insert_fresh t key v;
        t.length <- t.length + 1

  let iter t ~f =
    let keys = t.keys in
    let vals = t.vals in
    for i = 0 to Array.length keys - 1 do
      let k = keys.![i] in
      if not (K.equal k K.empty_sentinel) then
        f vals.?[i]
    done

  let iter_keys t ~f =
    let keys = t.keys in
    for i = 0 to Array.length keys - 1 do
      let k = keys.![i] in
      if not (K.equal k K.empty_sentinel) then f k
    done

  let iteri t ~f =
    let keys = t.keys in
    let vals = t.vals in
    for i = 0 to Array.length keys - 1 do
      let k = keys.![i] in
      if not (K.equal k K.empty_sentinel) then
        f ~key:k ~data:vals.?[i]
    done

  let fold t ~init ~f =
    let keys = t.keys in
    let vals = t.vals in
    let acc = ref init in
    for i = 0 to Array.length keys - 1 do
      let k = keys.![i] in
      if not (K.equal k K.empty_sentinel) then
        acc := f ~key:k ~data:vals.?[i] !acc
    done;
    !acc

  let map_inplace t ~f =
    let keys = t.keys in
    let vals = t.vals in
    for i = 0 to Array.length keys - 1 do
      let k = keys.![i] in
      if not (K.equal k K.empty_sentinel) then
        vals.?[i] <- f vals.?[i]
    done

  let mapi_inplace t ~f =
    let keys = t.keys in
    let vals = t.vals in
    for i = 0 to Array.length keys - 1 do
      let k = keys.![i] in
      if not (K.equal k K.empty_sentinel) then
        vals.?[i] <- f ~key:k ~data:vals.?[i]
    done

  let keys t =
    fold t ~init:[] ~f:(fun ~key ~data:_ acc -> key :: acc)

  let data t =
    fold t ~init:[] ~f:(fun ~key:_ ~data acc -> data :: acc)

  let to_alist t =
    fold t ~init:[] ~f:(fun ~key ~data acc -> (key, data) :: acc)
end

module Make_set(K : Key) : Set with type key = K.t = struct
  type key = K.t

  type t = {
    mutable keys   : K.t array;
    mutable length : int;
    mutable mask   : int;
  }

  let create ?(capacity = initial_capacity) () =
    let cap = Int.(ceil_pow2 @@ max capacity initial_capacity) in {
      keys = Array.create ~len:cap K.empty_sentinel;
      length = 0;
      mask = cap - 1;
    }

  let clear t =
    Array.fill t.keys ~pos:0 ~len:(Array.length t.keys) K.empty_sentinel;
    t.length <- 0

  let length t = t.length
  let is_empty t = t.length = 0

  let probe_of mask key idx =
    let open K in
    probe_of ~to_int mask key idx
  [@@inline]

  let find_slot t key =
    let open K in
    find_slot ~to_int ~equal ~empty_sentinel t.mask t.keys key
  [@@inline]

  let mem t key = find_slot t key >= 0 [@@inline]

  let insert_fresh t key =
    let mask = t.mask in
    let keys = t.keys in
    let cur_key = ref key in
    let idx = ref (K.to_int key land mask) in
    let distance = ref 0 in
    let continue = ref true in
    while !continue do
      let k = keys.![!idx] in
      match () with
      | () when K.equal k K.empty_sentinel ->
        keys.![!idx] <- !cur_key;
        continue := false
      | () -> match probe_of mask k !idx with
        | distance' when distance' < !distance ->
          keys.![!idx] <- !cur_key;
          cur_key := k;
          distance := distance' + 1;
          idx := (!idx + 1) land mask
        | _ ->
          incr distance;
          idx := (!idx + 1) land mask
    done

  let resize t =
    let old_keys = t.keys in
    let new_cap = Array.length old_keys * 2 in
    t.keys <- Array.create ~len:new_cap K.empty_sentinel;
    t.mask <- new_cap - 1;
    for i = 0 to Array.length old_keys - 1 do
      let k = old_keys.![i] in
      if not (K.equal k K.empty_sentinel) then insert_fresh t k
    done

  let grow_if_needed t =
    let cap = Array.length t.keys in
    if (t.length + 1) * 4 > cap * 3 then resize t
  [@@inline]

  let strict_add t key = match find_slot t key with
    | i when i < 0 ->
      grow_if_needed t;
      insert_fresh t key;
      t.length <- t.length + 1;
      true
    | _ -> false

  let add t key = ignore (strict_add t key) [@@inline]

  let shift_back t start =
    let mask = t.mask in
    let keys = t.keys in
    let idx = ref start in
    let continue = ref true in
    while !continue do
      let j = (!idx + 1) land mask in
      let kj = keys.![j] in
      match () with
      | () when K.equal kj K.empty_sentinel ->
        keys.![!idx] <- K.empty_sentinel;
        continue := false
      | () when probe_of mask kj j = 0 ->
        keys.![!idx] <- K.empty_sentinel;
        continue := false
      | () ->
        keys.![!idx] <- kj;
        idx := j
    done

  let remove t key = match find_slot t key with
    | i when i >= 0 ->
      shift_back t i;
      t.length <- t.length - 1
    | _ -> ()

  let iter t ~f =
    let keys = t.keys in
    for i = 0 to Array.length keys - 1 do
      let k = keys.![i] in
      if not (K.equal k K.empty_sentinel) then f k
    done

  let fold t ~init ~f =
    let keys = t.keys in
    let acc = ref init in
    for i = 0 to Array.length keys - 1 do
      let k = keys.![i] in
      if not (K.equal k K.empty_sentinel) then
        acc := f !acc k
    done;
    !acc

  let to_list t = fold t ~init:[] ~f:(fun acc k -> k :: acc)
end
