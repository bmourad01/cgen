open Core
open Regular.Std

module Oa = Option_array

type 'a t = {
  mutable data     : 'a Oa.t;
  mutable length   : int;
  mutable capacity : int;
}

let default_capacity = 7
let growth_factor = 2

let create ?(capacity = default_capacity) () = {
  data = Oa.create ~len:(max capacity 1);
  length = 0;
  capacity;
}

let length t = t.length
let is_empty t = t.length = 0
let capacity t = t.capacity
let copy t = {t with data = Oa.copy t.data}

let clear t =
  for i = 0 to t.length - 1 do
    Oa.unsafe_set_none t.data i;
  done;
  t.length <- 0

let append t1 t2 =
  if t2.length > 0 then begin
    let l1 = t1.length in
    let l2 = t2.length in
    let new_length = l1 + l2 in
    let dst = if t1.capacity < new_length then
        let dst = Oa.create ~len:new_length in
        Oa.unsafe_blit ~src:t1.data ~src_pos:0 ~dst ~dst_pos:0 ~len:l1;
        t1.data <- dst;
        t1.capacity <- new_length;
        dst
      else t1.data in
    Oa.unsafe_blit ~src:t2.data ~src_pos:0 ~dst ~dst_pos:l1 ~len:l2;
    t1.length <- new_length;
  end

let grow t =
  let new_capacity = t.capacity * growth_factor in
  let dst = Oa.create ~len:new_capacity in
  Oa.unsafe_blit ~src:t.data ~src_pos:0 ~dst ~dst_pos:0 ~len:t.length;
  t.data <- dst;
  t.capacity <- new_capacity

let unsafe_get t i = Oa.unsafe_get_some_assuming_some t.data i [@@inline]
let unsafe_set t i x = Oa.unsafe_set_some t.data i x [@@inline]

let push t x =
  let len = t.length in
  if t.capacity = len then grow t;
  unsafe_set t len x;
  t.length <- len + 1

let pop_exn t =
  let i = t.length - 1 in
  if i >= 0 then
    let x = unsafe_get t i in
    Oa.unsafe_set_none t.data i;
    t.length <- i;
    x
  else invalid_argf "pop_exn: empty" ()

let pop t = Option.try_with @@ fun () -> pop_exn t

let get_exn t i =
  if i >= 0 && i < t.length then unsafe_get t i
  else invalid_argf "get_exn: index %d out of bounds [0,%d)" i t.length ()

let get t i = Option.try_with @@ fun () -> get_exn t i

let front_exn t =
  if t.length > 0 then unsafe_get t 0 else invalid_argf "front_exn: empty" ()

let front t = Option.try_with @@ fun () -> front_exn t

let back_exn t =
  let i = t.length - 1 in
  if i >= 0 then unsafe_get t i else invalid_argf "back_exn: empty" ()

let back t = Option.try_with @@ fun () -> back_exn t

let set_exn t i x =
  if i >= 0 && i < t.length then unsafe_set t i x
  else invalid_argf "set_exn: index %d out of bounds [0,%d)" i t.length ()

let set t i x = try Ok (set_exn t i x) with
  | Invalid_argument msg -> Or_error.error_string msg

let fold_until =
  let open Container.Continue_or_stop in
  let rec loop t i acc ~f ~finish =
    if i < t.length then match f acc @@ unsafe_get t i with
      | Continue y -> loop t (i + 1) y ~f ~finish
      | Stop x -> x
    else finish acc in
  fun t ~init ~f ~finish -> (loop[@specialised]) t 0 init ~f ~finish

let foldi =
  let rec loop t i acc ~f =
    if i >= t.length then acc
    else loop t (i + 1) (f i acc @@ unsafe_get t i) ~f in
  fun t ~init ~f -> (loop[@specialised]) t 0 init ~f

let fold =
  let rec loop t i acc ~f =
    if i >= t.length then acc
    else loop t (i + 1) (f acc @@ unsafe_get t i) ~f in
  fun t ~init ~f -> (loop[@specialised]) t 0 init ~f

let fold_right =
  let rec loop t i acc ~f =
    if i < 0 then acc else loop t (i - 1) (f (unsafe_get t i) acc) ~f in
  fun t ~init ~f -> (loop[@specialised]) t (t.length - 1) init ~f

let iteri t ~f =
  for i = 0 to t.length - 1 do
    f i @@ unsafe_get t i
  done
[@@specialise]

let iter t ~f =
  for i = 0 to t.length - 1 do
    f @@ unsafe_get t i
  done
[@@specialise]

let iteri_rev t ~f =
  for i = t.length - 1 downto 0 do
    f i @@ unsafe_get t i
  done
[@@specialise]

let iter_rev t ~f =
  for i = t.length - 1 downto 0 do
    f @@ unsafe_get t i
  done
[@@specialise]

let findi =
  let rec loop t i ~f =
    if i < t.length then
      let x = unsafe_get t i in
      if f i x then Some x else loop t (i + 1) ~f
    else None in
  fun t ~f -> (loop[@specialised]) t 0 ~f

let find =
  let rec loop t i ~f =
    if i < t.length then
      let x = unsafe_get t i in
      if f x then Some x else loop t (i + 1) ~f
    else None in
  fun t ~f -> (loop[@specialised]) t 0 ~f

let find_mapi =
  let rec loop t i ~f =
    if i < t.length then match f i @@ unsafe_get t i with
      | None -> loop t (i + 1) ~f
      | Some _ as y -> y
    else None in
  fun t ~f -> (loop[@specialised]) t 0 ~f

let find_map =
  let rec loop t i ~f =
    if i < t.length then match f @@ unsafe_get t i with
      | None -> loop t (i + 1) ~f
      | Some _ as y -> y
    else None in
  fun t ~f -> (loop[@specialised]) t 0 ~f

let mapi_inplace t ~f =
  for i = 0 to t.length - 1 do
    unsafe_set t i @@ f i @@ unsafe_get t i
  done

let map_inplace t ~f =
  for i = 0 to t.length - 1 do
    unsafe_set t i @@ f @@ unsafe_get t i
  done

let mapi t ~f =
  let t' = create ~capacity:t.capacity () in
  for i = 0 to t.length - 1 do
    push t' @@ f i @@ unsafe_get t i
  done;
  t'

let map t ~f =
  let t' = create ~capacity:t.capacity () in
  for i = 0 to t.length - 1 do
    push t' @@ f @@ unsafe_get t i
  done;
  t'

let oldcap t = max default_capacity t.length

let filteri t ~f =
  let t' = create ~capacity:(oldcap t) () in
  iteri t ~f:(fun i x -> if f i x then push t' x);
  t'
[@@specialise]

let filter t ~f = filteri t ~f:(fun _ x -> f x)
[@@specialise]

let filter_mapi t ~f =
  let t' = create ~capacity:(oldcap t) () in
  iteri t ~f:(fun i x -> match f i x with
      | Some y -> push t' y
      | None -> ());
  t'
[@@specialise]

let filter_map t ~f = filter_mapi t ~f:(fun _ x -> f x)
[@@specialise]

let filteri_inplace t ~f =
  let j = ref 0 in
  for i = 0 to t.length - 1 do
    let x = unsafe_get t i in
    if f i x then begin
      if !j < i then unsafe_set t !j x;
      incr j
    end
  done;
  t.length <- !j
[@@specialise]

let filter_inplace t ~f = filteri_inplace t ~f:(fun _ x -> f x)
[@@specialise]

let remove_consecutive_duplicates t ~compare =
  let prev = ref None in
  filter_inplace t ~f:(fun x -> match !prev with
      | Some y when compare x y = 0 -> false
      | Some _ | None -> prev := Some x; true)
[@@specialise]

let to_array t = Array.init t.length ~f:(unsafe_get t)

let to_list t =
  let l = ref [] in
  for i = t.length - 1 downto 0 do
    l := unsafe_get t i :: !l
  done;
  !l

let to_list_rev t =
  let l = ref [] in
  for i = 0 to t.length - 1 do
    l := unsafe_get t i :: !l
  done;
  !l

let to_sequence_mutable t =
  Seq.unfold_step ~init:0 ~f:(fun i ->
      if i < t.length
      then Seq.Step.Yield (unsafe_get t i, i + 1)
      else Seq.Step.Done)

let to_sequence_rev_mutable t =
  Seq.unfold_step ~init:(t.length - 1) ~f:(fun i ->
      if i >= 0
      then Seq.Step.Yield (unsafe_get t i, i - 1)
      else Seq.Step.Done)

let to_sequence t = to_sequence_mutable @@ copy t
let to_sequence_rev t = to_sequence_rev_mutable @@ copy t

let of_array a =
  let length = Array.length a in
  let data = Oa.create ~len:length in
  Array.iteri a ~f:(Oa.unsafe_set_some data);
  {data; length; capacity = length}

let of_list l =
  let length = List.length l in
  let data = Oa.create ~len:length in
  List.iteri l ~f:(Oa.unsafe_set_some data);
  {data; length; capacity = length}

(* This is taken from the Array module in Jane Street's Base library. *)

module Sort = struct
  let get = Oa.get_some_exn
  let set = Oa.set_some

  let swap arr i j =
    let tmp = get arr i in
    set arr i (get arr j);
    set arr j tmp

  module Insertion_sort = struct
    let sort arr ~compare ~left ~right =
      for pos = left + 1 to right do
        let rec loop arr ~left ~compare i v =
          let i_next = i - 1 in
          if i_next >= left && compare (get arr i_next) v > 0 then begin
            set arr i (get arr i_next);
            loop arr ~left ~compare i_next v
          end else i in
        let v = get arr pos in
        let final_pos = loop arr ~left ~compare pos v in
        set arr final_pos v
      done
  end

  module Heap_sort = struct
    let rec heapify arr ~compare root ~left ~right =
      let relative_root = root - left in
      let left_child = (2 * relative_root) + left + 1 in
      let right_child = (2 * relative_root) + left + 2 in
      let largest =
        if left_child <= right
        && compare (get arr left_child) (get arr root) > 0
        then left_child else root in
      let largest =
        if right_child <= right
        && compare (get arr right_child) (get arr largest) > 0
        then right_child else largest in
      if largest <> root then begin
        swap arr root largest;
        heapify arr ~compare largest ~left ~right
      end

    let build_heap arr ~compare ~left ~right =
      for i = (left + right) / 2 downto left do
        heapify arr ~compare i ~left ~right
      done

    let sort arr ~compare ~left ~right =
      build_heap arr ~compare ~left ~right;
      for i = right downto left + 1 do
        swap arr left i;
        heapify arr ~compare left ~left ~right:(i - 1)
      done
  end

  module Intro_sort = struct
    let five_element_sort arr ~compare m1 m2 m3 m4 m5 =
      let compare_and_swap i j =
        if compare (get arr i) (get arr j) > 0 then swap arr i j in
      compare_and_swap m1 m2;
      compare_and_swap m4 m5;
      compare_and_swap m1 m3;
      compare_and_swap m2 m3;
      compare_and_swap m1 m4;
      compare_and_swap m3 m4;
      compare_and_swap m2 m5;
      compare_and_swap m2 m3;
      compare_and_swap m4 m5

    let choose_pivots arr ~compare ~left ~right =
      let sixth = (right - left) / 6 in
      let m1 = left + sixth in
      let m2 = m1 + sixth in
      let m3 = m2 + sixth in
      let m4 = m3 + sixth in
      let m5 = m4 + sixth in
      five_element_sort arr ~compare m1 m2 m3 m4 m5;
      let m2_val = get arr m2 in
      let m3_val = get arr m3 in
      let m4_val = get arr m4 in
      if compare m2_val m3_val = 0 then m2_val, m3_val, true
      else if compare m3_val m4_val = 0 then m3_val, m4_val, true
      else m2_val, m4_val, false

    let dual_pivot_partition arr ~compare ~left ~right =
      let pivot1, pivot2, pivots_equal =
        choose_pivots arr ~compare ~left ~right in
      let rec loop l p r =
        let pv = get arr p in
        if compare pv pivot1 < 0 then begin
          swap arr p l;
          cont (l + 1) (p + 1) r
        end else if compare pv pivot2 > 0 then
          (* loop invariants: same as those of the outer loop *)
          let rec scan_backwards r =
            if r > p && compare (get arr r) pivot2 > 0 
            then scan_backwards (r - 1) else r in
          let r = scan_backwards r in
          swap arr r p;
          cont l p (r - 1)
        else cont l (p + 1) r
      and cont l p r = if p > r then l, r else loop l p r in
      let l, r = cont left left right in
      l, r, pivots_equal

    let rec intro_sort arr ~max_depth ~compare ~left ~right =
      let len = right - left + 1 in
      if len <= 32 then Insertion_sort.sort arr ~compare ~left ~right
      else if max_depth < 0 then Heap_sort.sort arr ~compare ~left ~right
      else
        let max_depth = max_depth - 1 in
        let l, r, middle_sorted =
          dual_pivot_partition arr ~compare ~left ~right in
        intro_sort arr ~max_depth ~compare ~left ~right:(l - 1);
        if not middle_sorted then
          intro_sort arr ~max_depth ~compare ~left:l ~right:r;
        intro_sort arr ~max_depth ~compare ~left:(r + 1) ~right

    let log10_of_3 = Caml.log10 3.
    let log3 x = Caml.log10 x /. log10_of_3

    let sort arr ~compare ~left ~right =
      let len = right - left + 1 in
      if len > 0 then
        let max_depth = Int.of_float (log3 (Int.to_float len)) in
        intro_sort arr ~max_depth ~compare ~left ~right
  end
end

let sort ?pos ?len t ~compare =
  let pos, len = Ordered_collection_common.get_pos_len_exn ()
      ?pos ?len ~total_length:t.length in
  Sort.Intro_sort.sort t.data ~compare ~left:pos ~right:(pos + len - 1)

let dedup_and_sort t ~compare =
  sort t ~compare;
  remove_consecutive_duplicates t ~compare
[@@specialise]
