(* Port of the Haskell `rrb-vector` implementation. *)

open Core

module Seq = Sequence

module Buffer = struct
  type 'a t = {
    buf : 'a Option_array.t;
    mutable off : int;
  }

  let create len = {
    buf = Option_array.create ~len;
    off = 0;
  }

  let push t x =
    Option_array.set_some t.buf t.off x;
    t.off <- t.off + 1

  let get t =
    let result = Array.init t.off ~f:(Option_array.get_some_exn t.buf) in
    t.off <- 0;
    result

  let push_to_if_nonempty f from to_ =
    if from.off > 0 then push to_ @@ f @@ get from

  let length t = t.off
end

let hash_fold_array f state t =
  Array.fold t ~init:(hash_fold_int state (Array.length t)) ~f

type 'a tree =
  | Balanced of 'a tree array
  | Unbalanced of 'a tree array * int array
  | Leaf of 'a array
[@@deriving bin_io, hash, sexp]

type 'a t =
  | Empty
  | Root of {
      size  : int;
      shift : int;
      tree  : 'a tree;
    }
[@@deriving bin_io, hash, sexp]

exception Out_of_bounds

(* The Haskell implementation uses a block size of 16, but that is
   likely due to specifics of GHC and how it handles allocations of
   lazy values. For strict languages (like OCaml) the sweet spot
   seems to be 32. *)
let block_shift = 5
let block_size = 1 lsl block_shift
let block_mask = block_size - 1

let up sh = sh + block_shift
let down sh = sh - block_shift
let radix_index i sh = (i asr sh) land block_mask

let length = function
  | Empty -> 0
  | Root r -> r.size

let is_empty = function
  | Empty -> true
  | Root _ -> false

let relaxed_radix_index sizes i sh =
  let rec loop idx = if i < sizes.(idx) then idx else loop (idx + 1) in
  let guess = radix_index i sh in
  let idx = loop guess in
  let sub_idx = if idx = 0 then i else i - sizes.(idx - 1) in
  idx, sub_idx

let tree_to_array = function
  | Balanced arr -> arr
  | Unbalanced (arr, _) -> arr
  | Leaf _ -> failwith "tree_to_array: Leaf"

let tree_balanced = function
  | Balanced _ -> true
  | Unbalanced _ -> false
  | Leaf _ -> true

let tree_size sh t =
  let rec go acc sh = function
    | Leaf arr -> acc + Array.length arr
    | Unbalanced (arr, sizes) -> acc + sizes.(Array.length arr - 1)
    | Balanced arr ->
      let i = Array.length arr - 1 in
      let acc' = acc + i * (1 lsl sh) and sh' = down sh in
      go acc' sh' arr.(i) in
  go 0 sh t

let compute_sizes sh arr =
  let max_size = 1 lsl sh in
  let len = Array.length arr in
  let lenm1 = len - 1 in
  let is_balanced =
    let rec go i =
      if i < lenm1 then
        tree_size (down sh) arr.(i) = max_size && go (i + 1)
      else tree_balanced arr.(i) in
    go 0 in
  if is_balanced then Balanced arr else
    let acc = ref 0 in
    let sizes = Array.init len ~f:(fun i ->
        let size = tree_size (down sh) arr.(i) in
        acc := !acc + size;
        !acc) in
    Unbalanced (arr, sizes)

let empty = Empty

let singleton x = Root {
    size = 1;
    shift = 0;
    tree = Leaf [|x|];
  }

let rec get_tree i sh = function
  | Balanced arr -> get_tree i (down sh) arr.(radix_index i sh)
  | Unbalanced (arr, sizes) ->
    let idx, sub_idx = relaxed_radix_index sizes i sh in
    get_tree sub_idx (down sh) arr.(idx)
  | Leaf arr -> arr.(i land block_mask)

let get t i = match t with
  | Empty -> None
  | Root _ when i < 0 -> None
  | Root r when i >= r.size -> None
  | Root r -> Some (get_tree i r.shift r.tree)

let get_exn t i = match get t i with
  | None -> raise Out_of_bounds
  | Some x -> x

let rec set_tree x i sh = function
  | Balanced arr ->
    let arr' = Array.copy arr in
    let idx = radix_index i sh in
    arr'.(idx) <- set_tree x i (down sh) arr.(idx);
    Balanced arr'
  | Unbalanced (arr, sizes) ->
    let idx, sub_idx = relaxed_radix_index sizes i sh in
    let arr' = Array.copy arr in
    arr'.(idx) <- set_tree x sub_idx (down sh) arr.(idx);
    Unbalanced (arr', sizes)
  | Leaf arr ->
    let arr' = Array.copy arr in
    arr'.(i land block_mask) <- x;
    Leaf arr'

let set t i x = match t with
  | Empty -> Empty
  | Root _ when i < 0 -> t
  | Root r when i >= r.size -> t
  | Root r -> Root {r with tree = set_tree x i r.shift r.tree}

let rec update_tree f i sh = function
  | Balanced arr ->
    let arr' = Array.copy arr in
    let idx = radix_index i sh in
    arr'.(idx) <- update_tree f i (down sh) arr.(idx);
    Balanced arr'
  | Unbalanced (arr, sizes) ->
    let idx, sub_idx = relaxed_radix_index sizes i sh in
    let arr' = Array.copy arr in
    arr'.(idx) <- update_tree f sub_idx (down sh) arr.(idx);
    Unbalanced (arr', sizes)
  | Leaf arr ->
    let arr' = Array.copy arr in
    let idx = i land block_mask in
    arr'.(idx) <- f arr.(idx);
    Leaf arr'

let update t i ~f = match t with
  | Empty -> Empty
  | Root _ when i < 0 -> t
  | Root r when i >= r.size -> t
  | Root r -> Root {r with tree = update_tree f i r.shift r.tree}

let rec map_tree t ~f = match t with
  | Balanced arr ->
    Balanced (Array.map arr ~f:(map_tree ~f))
  | Unbalanced (arr, sizes) ->
    Unbalanced (Array.map arr ~f:(map_tree ~f), sizes)
  | Leaf arr -> Leaf (Array.map arr ~f)

let map t ~f = match t with
  | Root r -> Root {r with tree = map_tree r.tree ~f}
  | Empty -> Empty

let rec iter_tree t ~f = match t with
  | Balanced arr | Unbalanced (arr, _) -> Array.iter arr ~f:(iter_tree ~f)
  | Leaf arr -> Array.iter arr ~f

let iter t ~f = match t with
  | Root r -> iter_tree r.tree ~f
  | Empty -> ()

let rec iter_rev_tree t ~f = match t with
  | Balanced arr | Unbalanced (arr, _) ->
    for i = Array.length arr - 1 downto 0 do iter_rev_tree arr.(i) ~f done
  | Leaf arr ->
    for i = Array.length arr - 1 downto 0 do f arr.(i) done

let iter_rev t ~f = match t with
  | Root r -> iter_rev_tree r.tree ~f
  | Empty -> ()

let rec exists_tree t ~f = match t with
  | Balanced arr | Unbalanced (arr, _) -> Array.exists arr ~f:(exists_tree ~f)
  | Leaf arr -> Array.exists arr ~f

let exists t ~f = match t with
  | Root r -> exists_tree r.tree ~f
  | Empty -> false

let rec find_tree t ~f = match t with
  | Balanced arr | Unbalanced (arr, _) -> Array.find_map arr ~f:(find_tree ~f)
  | Leaf arr -> Array.find arr ~f

let find t ~f = match t with
  | Root r -> find_tree r.tree ~f
  | Empty -> None

let rec fold_tree t init ~f = match t with
  | Balanced arr | Unbalanced (arr, _) ->
    Array.fold arr ~init ~f:(fun acc x -> fold_tree x acc ~f)
  | Leaf arr -> Array.fold arr ~init ~f

let fold t ~init ~f = match t with
  | Root r -> fold_tree r.tree init ~f
  | Empty -> init

let foldi t ~init ~f =
  let i = ref 0 in
  fold t ~init ~f:(fun acc x ->
      let acc' = f !i acc x in
      Int.incr i;
      acc')

(* The index of the first element satisfying [f], if any (short-circuits). *)
let find_index t ~f =
  let exception Found of int in
  try
    foldi t ~init:() ~f:(fun i () x ->
        if f x then raise_notrace (Found i));
    None
  with Found i -> Some i

let rec fold_right_tree t init ~f = match t with
  | Balanced arr | Unbalanced (arr, _) ->
    Array.fold_right arr ~init ~f:(fold_right_tree ~f)
  | Leaf arr -> Array.fold_right arr ~init ~f

let fold_right t ~init ~f = match t with
  | Root r -> fold_right_tree r.tree init ~f
  | Empty -> init

let to_list t = fold_right t ~init:[] ~f:(fun x acc -> x :: acc)
let to_list_rev t = fold t ~init:[] ~f:(fun acc x -> x :: acc)

(* Groups a list of subtrees into chunks of `block_size`, applying `f` to
   each chunk's array.

   We manually unroll to reduce intermediate allocations, and maximize
   throughput.
*)
let[@tail_mod_cons] rec nodes f = function
  | [] -> []
  | [x0] ->
    [f [|x0|]]
  | [x0; x1] ->
    [f [|x0; x1|]]
  | [x0; x1; x2] ->
    [f [|x0; x1; x2|]]
  | [x0; x1; x2; x3] ->
    [f [|x0; x1; x2; x3|]]
  | [x0; x1; x2; x3; x4] ->
    [f [|x0; x1; x2; x3; x4|]]
  | [x0; x1; x2; x3; x4; x5] ->
    [f [|x0; x1; x2; x3; x4; x5|]]
  | [x0; x1; x2; x3; x4; x5; x6] ->
    [f [|x0; x1; x2; x3; x4; x5; x6|]]
  | [x0; x1; x2; x3; x4; x5; x6; x7] ->
    [f [|x0; x1; x2; x3; x4; x5; x6; x7|]]
  | [x0; x1; x2; x3; x4; x5; x6; x7;
     x8] ->
    [f [|x0; x1; x2; x3; x4; x5; x6; x7;
         x8|]]
  | [x0; x1; x2; x3; x4; x5; x6; x7;
     x8; x9] ->
    [f [|x0; x1; x2; x3; x4; x5; x6; x7;
         x8; x9|]]
  | [x0; x1; x2; x3; x4; x5; x6; x7;
     x8; x9; x10] ->
    [f [|x0; x1; x2; x3; x4; x5; x6; x7;
         x8; x9; x10|]]
  | [x0; x1; x2; x3; x4; x5; x6; x7;
     x8; x9; x10; x11] ->
    [f [|x0; x1; x2; x3; x4; x5; x6; x7;
         x8; x9; x10; x11|]]
  | [x0; x1; x2; x3; x4; x5; x6; x7;
     x8; x9; x10; x11; x12] ->
    [f [|x0; x1; x2; x3; x4; x5; x6; x7;
         x8; x9; x10; x11; x12|]]
  | [x0; x1; x2; x3; x4; x5; x6; x7;
     x8; x9; x10; x11; x12; x13] ->
    [f [|x0; x1; x2; x3; x4; x5; x6; x7;
         x8; x9; x10; x11; x12; x13|]]
  | [x0; x1; x2; x3; x4; x5; x6; x7;
     x8; x9; x10; x11; x12; x13; x14] ->
    [f [|x0; x1; x2; x3; x4; x5; x6; x7;
         x8; x9; x10; x11; x12; x13; x14|]]
  | [x0; x1; x2; x3; x4; x5; x6; x7;
     x8; x9; x10; x11; x12; x13; x14; x15] ->
    [f [|x0; x1; x2; x3; x4; x5; x6; x7;
         x8; x9; x10; x11; x12; x13; x14; x15|]]
  | [x0; x1; x2; x3; x4; x5; x6; x7;
     x8; x9; x10; x11; x12; x13; x14; x15;
     x16] ->
    [f [|x0; x1; x2; x3; x4; x5; x6; x7;
         x8; x9; x10; x11; x12; x13; x14; x15;
         x16|]]
  | [x0; x1; x2; x3; x4; x5; x6; x7;
     x8; x9; x10; x11; x12; x13; x14; x15;
     x16; x17] ->
    [f [|x0; x1; x2; x3; x4; x5; x6; x7;
         x8; x9; x10; x11; x12; x13; x14; x15;
         x16; x17|]]
  | [x0; x1; x2; x3; x4; x5; x6; x7;
     x8; x9; x10; x11; x12; x13; x14; x15;
     x16; x17; x18] ->
    [f [|x0; x1; x2; x3; x4; x5; x6; x7;
         x8; x9; x10; x11; x12; x13; x14; x15;
         x16; x17; x18|]]
  | [x0; x1; x2; x3; x4; x5; x6; x7;
     x8; x9; x10; x11; x12; x13; x14; x15;
     x16; x17; x18; x19] ->
    [f [|x0; x1; x2; x3; x4; x5; x6; x7;
         x8; x9; x10; x11; x12; x13; x14; x15;
         x16; x17; x18; x19|]]
  | [x0; x1; x2; x3; x4; x5; x6; x7;
     x8; x9; x10; x11; x12; x13; x14; x15;
     x16; x17; x18; x19; x20] ->
    [f [|x0; x1; x2; x3; x4; x5; x6; x7;
         x8; x9; x10; x11; x12; x13; x14; x15;
         x16; x17; x18; x19; x20|]]
  | [x0; x1; x2; x3; x4; x5; x6; x7;
     x8; x9; x10; x11; x12; x13; x14; x15;
     x16; x17; x18; x19; x20; x21] ->
    [f [|x0; x1; x2; x3; x4; x5; x6; x7;
         x8; x9; x10; x11; x12; x13; x14; x15;
         x16; x17; x18; x19; x20; x21|]]
  | [x0; x1; x2; x3; x4; x5; x6; x7;
     x8; x9; x10; x11; x12; x13; x14; x15;
     x16; x17; x18; x19; x20; x21; x22] ->
    [f [|x0; x1; x2; x3; x4; x5; x6; x7;
         x8; x9; x10; x11; x12; x13; x14; x15;
         x16; x17; x18; x19; x20; x21; x22|]]
  | [x0; x1; x2; x3; x4; x5; x6; x7;
     x8; x9; x10; x11; x12; x13; x14; x15;
     x16; x17; x18; x19; x20; x21; x22; x23] ->
    [f [|x0; x1; x2; x3; x4; x5; x6; x7;
         x8; x9; x10; x11; x12; x13; x14; x15;
         x16; x17; x18; x19; x20; x21; x22; x23|]]
  | [x0; x1; x2; x3; x4; x5; x6; x7;
     x8; x9; x10; x11; x12; x13; x14; x15;
     x16; x17; x18; x19; x20; x21; x22; x23;
     x24] ->
    [f [|x0; x1; x2; x3; x4; x5; x6; x7;
         x8; x9; x10; x11; x12; x13; x14; x15;
         x16; x17; x18; x19; x20; x21; x22; x23;
         x24|]]
  | [x0; x1; x2; x3; x4; x5; x6; x7;
     x8; x9; x10; x11; x12; x13; x14; x15;
     x16; x17; x18; x19; x20; x21; x22; x23;
     x24; x25] ->
    [f [|x0; x1; x2; x3; x4; x5; x6; x7;
         x8; x9; x10; x11; x12; x13; x14; x15;
         x16; x17; x18; x19; x20; x21; x22; x23;
         x24; x25|]]
  | [x0; x1; x2; x3; x4; x5; x6; x7;
     x8; x9; x10; x11; x12; x13; x14; x15;
     x16; x17; x18; x19; x20; x21; x22; x23;
     x24; x25; x26] ->
    [f [|x0; x1; x2; x3; x4; x5; x6; x7;
         x8; x9; x10; x11; x12; x13; x14; x15;
         x16; x17; x18; x19; x20; x21; x22; x23;
         x24; x25; x26|]]
  | [x0; x1; x2; x3; x4; x5; x6; x7;
     x8; x9; x10; x11; x12; x13; x14; x15;
     x16; x17; x18; x19; x20; x21; x22; x23;
     x24; x25; x26; x27] ->
    [f [|x0; x1; x2; x3; x4; x5; x6; x7;
         x8; x9; x10; x11; x12; x13; x14; x15;
         x16; x17; x18; x19; x20; x21; x22; x23;
         x24; x25; x26; x27|]]
  | [x0; x1; x2; x3; x4; x5; x6; x7;
     x8; x9; x10; x11; x12; x13; x14; x15;
     x16; x17; x18; x19; x20; x21; x22; x23;
     x24; x25; x26; x27; x28] ->
    [f [|x0; x1; x2; x3; x4; x5; x6; x7;
         x8; x9; x10; x11; x12; x13; x14; x15;
         x16; x17; x18; x19; x20; x21; x22; x23;
         x24; x25; x26; x27; x28|]]
  | [x0; x1; x2; x3; x4; x5; x6; x7;
     x8; x9; x10; x11; x12; x13; x14; x15;
     x16; x17; x18; x19; x20; x21; x22; x23;
     x24; x25; x26; x27; x28; x29] ->
    [f [|x0; x1; x2; x3; x4; x5; x6; x7;
         x8; x9; x10; x11; x12; x13; x14; x15;
         x16; x17; x18; x19; x20; x21; x22; x23;
         x24; x25; x26; x27; x28; x29|]]
  | [x0; x1; x2; x3; x4; x5; x6; x7;
     x8; x9; x10; x11; x12; x13; x14; x15;
     x16; x17; x18; x19; x20; x21; x22; x23;
     x24; x25; x26; x27; x28; x29; x30] ->
    [f [|x0; x1; x2; x3; x4; x5; x6; x7;
         x8; x9; x10; x11; x12; x13; x14; x15;
         x16; x17; x18; x19; x20; x21; x22; x23;
         x24; x25; x26; x27; x28; x29; x30|]]
  | x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7
    :: x8 :: x9 :: x10 :: x11 :: x12 :: x13 :: x14 :: x15
    :: x16 :: x17 :: x18 :: x19 :: x20 :: x21 :: x22 :: x23
    :: x24 :: x25 :: x26 :: x27 :: x28 :: x29 :: x30 :: x31 :: rest ->
    f [|
      x0; x1; x2; x3; x4; x5; x6; x7;
      x8; x9; x10; x11; x12; x13; x14; x15;
      x16; x17; x18; x19; x20; x21; x22; x23;
      x24; x25; x26; x27; x28; x29; x30; x31
    |] :: nodes f rest

(* Builds the upper levels of the tree from its leaf nodes. *)
let build_from_leaves = function
  | [tree] -> Root {
      size = tree_size 0 tree;
      shift = 0;
      tree;
    }
  | leaves ->
    let rec iter sh trees =
      match nodes (fun x -> Balanced x) trees with
      | [tree] -> Root {
          size = tree_size sh tree;
          shift = sh;
          tree;
        }
      | trees' -> iter (up sh) trees' in
    iter block_shift leaves

let of_list = function
  | [] -> Empty
  | [x] -> singleton x
  | xs -> build_from_leaves @@ nodes (fun x -> Leaf x) xs

let init n ~f =
  if n <= 0 then Empty
  else if n = 1 then singleton (f 0)
  else
    let num_leaves = (n + block_mask) / block_size in
    build_from_leaves @@ List.init num_leaves ~f:(fun li ->
        let base = li * block_size in
        let len = Int.min block_size (n - base) in
        Leaf (Array.init len ~f:(fun j -> f (base + j))))

(* Builds a vector by streaming elements through [push_all], chunking them
   into leaves directly (no intermediate list of elements). *)
let build_streaming push_all =
  let buf = Buffer.create block_size in
  let leaves = ref [] in
  push_all (fun x ->
      if Buffer.length buf = block_size then
        leaves := Leaf (Buffer.get buf) :: !leaves;
      Buffer.push buf x);
  if Buffer.length buf > 0 then
    leaves := Leaf (Buffer.get buf) :: !leaves;
  match List.rev !leaves with
  | [] -> Empty
  | leaves -> build_from_leaves leaves

let filter t ~f =
  build_streaming @@ fun push -> iter t ~f:(fun x -> if f x then push x)

let filter_map t ~f =
  build_streaming @@ fun push ->
  iter t ~f:(fun x -> match f x with Some y -> push y | None -> ())

let of_sequence seq =
  build_streaming @@ fun push -> Seq.iter seq ~f:push

let to_sequence =
  let open Seq.Generator in
  let rec go = function
    | Balanced arr | Unbalanced (arr, _) ->
      Array.to_sequence_mutable arr |>
      Seq.fold ~init:(return ())
        ~f:(fun acc x -> acc >>= fun () -> go x)
    | Leaf arr -> of_sequence (Array.to_sequence_mutable arr) in
  function
  | Empty -> Seq.empty
  | Root r -> run @@ go r.tree

let equal f t1 t2 =
  length t1 = length t2 &&
  Seq.equal f (to_sequence t1) (to_sequence t2)

let compare f t1 t2 =
  (* We won't compare length here, to keep the semantics in line
     with how List.compare behaves. *)
  Seq.compare f (to_sequence t1) (to_sequence t2)

let array_seq_rev arr =
  let open Seq.Generator in
  let rec go arr i =
    if i < 0 then return () else
      yield arr.(i) >>= fun () ->
      go arr (i - 1) in
  run @@ go arr (Array.length arr - 1)

let to_sequence_rev =
  let open Seq.Generator in
  let rec go = function
    | Balanced arr | Unbalanced (arr, _) ->
      let rec go2 arr i =
        if i < 0 then return () else
          go arr.(i) >>= fun () ->
          go2 arr (i - 1) in
      go2 arr (Array.length arr - 1)
    | Leaf arr -> of_sequence (array_seq_rev arr) in
  function
  | Empty -> Seq.empty
  | Root r -> run @@ go r.tree

let rec normalize = function
  | Root {size; shift; tree = Balanced arr | Unbalanced (arr, _)}
    when Array.length arr = 1 -> normalize @@ Root {
      size; shift = down shift; tree = arr.(0)
    }
  | t -> t

let rec take_tree i sh = function
  | Balanced arr ->
    let idx = radix_index i sh in
    let arr' = Array.subo arr ~len:(idx + 1) in
    arr'.(idx) <- take_tree i (down sh) arr'.(idx);
    Balanced arr'
  | Unbalanced (arr, sizes) ->
    let idx, sub_idx = relaxed_radix_index sizes i sh in
    let arr' = Array.subo arr ~len:(idx + 1) in
    arr'.(idx) <- take_tree sub_idx (down sh) arr'.(idx);
    compute_sizes sh arr'
  | Leaf arr -> Leaf (Array.subo arr ~len:((i land block_mask) + 1))

let take t n = match t with
  | Empty -> Empty
  | Root _ when n <= 0 -> Empty
  | Root r when n >= r.size -> t
  | Root r -> normalize @@ Root {
      r with size = n; tree = take_tree (n - 1) r.shift r.tree
    }

let rec drop_tree n sh = function
  | Balanced arr ->
    let idx = radix_index n sh in
    let arr' = Array.subo arr ~pos:idx in
    arr'.(0) <- drop_tree n (down sh) arr'.(0);
    compute_sizes sh arr'
  | Unbalanced (arr, sizes) ->
    let idx, sub_idx = relaxed_radix_index sizes n sh in
    let arr' = Array.subo arr ~pos:idx in
    arr'.(0) <- drop_tree sub_idx (down sh) arr'.(0);
    compute_sizes sh arr'
  | Leaf arr -> Leaf (Array.subo arr ~pos:(n land block_mask))

let drop t n = match t with
  | Empty -> Empty
  | Root _ when n <= 0 -> t
  | Root r when n >= r.size -> Empty
  | Root r -> normalize @@ Root {
      r with size = r.size - n; tree = drop_tree n r.shift r.tree
    }

let split_at t n = match t with
  | Empty -> Empty, Empty
  | Root _ when n <= 0 -> empty, t
  | Root r when n >= r.size -> t, empty
  | Root r ->
    normalize @@ Root {
      r with size = n; tree = take_tree (n - 1) r.shift r.tree;
    },
    normalize @@ Root {
      r with size = r.size - n; tree = drop_tree n r.shift r.tree;
    }

let rec new_branch x = function
  | 0 -> Leaf [|x|]
  | sh -> Balanced [|new_branch x (down sh)|]

let array_cons x arr =
  let len = Array.length arr in
  let arr' = Array.create ~len:(len + 1) x in
  Array.blit ~src:arr ~src_pos:0 ~dst:arr' ~dst_pos:1 ~len;
  arr'

let array_snoc x arr =
  let len = Array.length arr in
  let arr' = Array.create ~len:(len + 1) x in
  Array.blit ~src:arr ~src_pos:0 ~dst:arr' ~dst_pos:0 ~len;
  arr'

let rec cons_tree x sh insert_sh = function
  | Balanced arr | Unbalanced (arr, _) when sh = insert_sh ->
    compute_sizes sh (array_cons (new_branch x (down sh)) arr)
  | Balanced arr | Unbalanced (arr, _) ->
    let arr' = Array.copy arr in
    arr'.(0) <- cons_tree x (down sh) insert_sh arr'.(0);
    compute_sizes sh arr'
  | Leaf arr -> Leaf (array_cons x arr)

let cons x = function
  | Empty -> singleton x
  | Root r ->
    let insert_sh =
      let rec go sz sh min = function
        | Balanced _ ->
          let hi_sh = Int.max ((Int.floor_log2 (sz - 1) / block_shift) * block_shift) 0 in
          let hi = (sz - 1) asr hi_sh in
          let new_sh = if hi < block_mask then hi_sh else hi_sh + block_shift in
          if new_sh > sh then min else new_sh
        | Unbalanced (arr, sizes) ->
          let sz' = sizes.(0) in
          let new_min = if Array.length arr < block_size then sh else min in
          go sz' (down sh) new_min arr.(0)
        | Leaf arr -> if Array.length arr < block_size then 0 else min in
      go r.size r.shift (up r.shift) r.tree in
    if insert_sh > r.shift then
      Root {
        size = r.size + 1;
        shift = insert_sh;
        tree = compute_sizes insert_sh [|
            new_branch x r.shift;
            r.tree;
          |];
      }
    else
      Root {
        r with
        size = r.size + 1;
        tree = cons_tree x r.shift insert_sh r.tree;
      }

let new_sizes_snoc arr =
  let len = Array.length arr in
  let lenm1 = len - 1 in
  let last_size = arr.(lenm1) in
  let new_arr = Array.create ~len:(len + 1) (last_size + 1) in
  Array.blit ~src:arr ~src_pos:0 ~dst:new_arr ~dst_pos:0 ~len;
  new_arr

let new_sizes_adjust arr =
  let len = Array.length arr in
  let lenm1 = len - 1 in
  let new_arr = Array.copy arr in
  let last_size = arr.(lenm1) in
  new_arr.(lenm1) <- last_size + 1;
  new_arr

let rec snoc_tree x sh insert_sh = function
  | Balanced arr when sh = insert_sh ->
    Balanced (array_snoc (new_branch x (down sh)) arr)
  | Unbalanced (arr, sizes) when sh = insert_sh ->
    Unbalanced (
      array_snoc (new_branch x (down sh)) arr,
      new_sizes_snoc sizes
    )
  | Balanced arr ->
    let arr' = Array.copy arr in
    let lenm1 = Array.length arr - 1 in
    arr'.(lenm1) <- snoc_tree x (down sh) insert_sh arr'.(lenm1);
    Balanced arr'
  | Unbalanced (arr, sizes) ->
    let arr' = Array.copy arr in
    let lenm1 = Array.length arr - 1 in
    arr'.(lenm1) <- snoc_tree x (down sh) insert_sh arr'.(lenm1);
    Unbalanced (arr', new_sizes_adjust sizes)
  | Leaf arr -> Leaf (array_snoc x arr)

let snoc t x = match t with
  | Empty -> singleton x
  | Root r ->
    let insert_sh =
      let rec go sz sh min = function
        | Balanced _ ->
          let new_sh = (Int.ctz sz / block_shift) * block_shift in
          if new_sh > sh then min else new_sh
        | Unbalanced (arr, sizes) ->
          let len = Array.length arr in
          let last_idx = len - 1 in
          let sz' = sizes.(last_idx) - sizes.(last_idx - 1) in
          let new_min = if len < block_size then sh else min in
          go sz' (down sh) new_min arr.(last_idx)
        | Leaf arr -> if Array.length arr < block_size then 0 else min in
      go r.size r.shift (up r.shift) r.tree in
    if insert_sh > r.shift then
      Root {
        size = r.size + 1;
        shift = insert_sh;
        tree = compute_sizes insert_sh [|
            r.tree;
            new_branch x r.shift;
          |];
      }
    else
      Root {
        r with
        size = r.size + 1;
        tree = snoc_tree x r.shift insert_sh r.tree;
      }

let merge_leaves t1 arr1 t2 arr2 =
  let len1 = Array.length arr1 in
  if len1 = block_size then
    [|t1; t2|]
  else
    let len2 = Array.length arr2 in
    let arr = Array.append arr1 arr2 in
    if len1 + len2 <= block_size then
      [|Leaf arr|]
    else
      let left = Array.subo arr ~len:block_size in
      let right = Array.subo arr ~pos:block_size in
      [|Leaf left; Leaf right|]

let view_left_arr a = a.(0), Array.subo a ~pos:1

let view_right_arr a =
  let n = Array.length a - 1 in
  Array.subo a ~len:n, a.(n)

let merge_rebalance0 ~extract ~construct sh left center right =
  let new_root = Buffer.create block_size in
  let new_subtree = Buffer.create block_size in
  let new_node = Buffer.create block_size in
  let process_subtree subtree =
    extract subtree |> Array.iter ~f:(fun x ->
        let len_node = Buffer.length new_node in
        if len_node = block_size then begin
          Buffer.push_to_if_nonempty construct new_node new_subtree;
          let len_subtree = Buffer.length new_subtree in
          if len_subtree = block_size then
            Buffer.push_to_if_nonempty (compute_sizes sh) new_subtree new_root;
        end;
        Buffer.push new_node x) in
  Array.iter left ~f:process_subtree;
  Array.iter center ~f:process_subtree;
  Array.iter right ~f:process_subtree;
  Buffer.push_to_if_nonempty construct new_node new_subtree;
  Buffer.push_to_if_nonempty (compute_sizes sh) new_subtree new_root;
  Buffer.get new_root

let merge_rebalance sh left center right =
  if sh = block_shift then
    merge_rebalance0
      ~extract:(function
          | Leaf arr -> arr
          | _ -> failwith "merge_rebalance: extract on non-Leaf")
      ~construct:(fun arr -> Leaf arr)
      sh left center right
  else
    merge_rebalance0
      ~extract:tree_to_array
      ~construct:(compute_sizes @@ down sh)
      sh left center right

let rec merge_trees t1 sh1 t2 sh2 = match t1, t2 with
  | Leaf arr1, Leaf arr2 -> merge_leaves t1 arr1 t2 arr2
  | _ -> match Int.compare sh1 sh2 with
    | n when n < 0 ->
      let right = tree_to_array t2 in
      let right_hd, right_tl = view_left_arr right in
      let merged = merge_trees t1 sh1 right_hd (down sh2) in
      merge_rebalance sh2 [||] merged right_tl
    | n when n > 0 ->
      let left = tree_to_array t1 in
      let left_init, left_last = view_right_arr left in
      let merged = merge_trees left_last (down sh1) t2 sh2 in
      merge_rebalance sh1 left_init merged [||]
    | _ ->
      let left = tree_to_array t1 in
      let right = tree_to_array t2 in
      let left_init, left_last = view_right_arr left in
      let right_hd, right_tl = view_left_arr right in
      let merged = merge_trees left_last (down sh1) right_hd (down sh2) in
      merge_rebalance sh1 left_init merged right_tl

let append t1 t2 = match t1, t2 with
  | Empty, _ -> t2
  | _, Empty -> t1
  | Root r1, Root r2 ->
    let up_max_sh = up (Int.max r1.shift r2.shift) in
    let new_arr = merge_trees r1.tree r1.shift r2.tree r2.shift in
    normalize @@ Root {
      size = r1.size + r2.size;
      shift = up_max_sh;
      tree = compute_sizes up_max_sh new_arr;
    }

(* Splice [xs] in immediately before the first element of [t] satisfying
   [f] (or return [t] unchanged if there is none), using the logarithmic
   split/append rather than materializing a list. *)
let insert_before t xs ~f = match find_index t ~f with
  | None -> t
  | Some i ->
    let l, r = split_at t i in
    append l (append xs r)

(* As [insert_before], but after the matching element. *)
let insert_after t xs ~f = match find_index t ~f with
  | None -> t
  | Some i ->
    let l, r = split_at t (i + 1) in
    append l (append xs r)
