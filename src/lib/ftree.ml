(* Implementation of a finger tree data structure, adapted from Batteries:

   https://github.com/ocaml-batteries-team/batteries-included/blob/master/src/batFingerTree.ml
*)

open Core
open Regular.Std

type 'a monoid = {
  zero : 'a;
  combine : 'a -> 'a -> 'a;
}

module Generic = struct
  type ('a, 'm) digit =
    | One of 'm * 'a
    | Two of 'm * 'a * 'a
    | Three of 'm * 'a * 'a * 'a
    | Four of 'm * 'a * 'a * 'a * 'a
  [@@deriving bin_io, sexp]

  type ('a, 'm) node =
    | Node2 of 'm * 'a * 'a
    | Node3 of 'm * 'a * 'a * 'a
  [@@deriving bin_io, sexp]

  type ('a, 'm) t =
    | Nil
    | Single of 'a
    | Deep of 'm * ('a, 'm) digit * (('a, 'm) node, 'm) t * ('a, 'm) digit
  [@@deriving bin_io, sexp]

  let empty = Nil
  let singleton a = Single a

  let is_empty = function
    | Single _ | Deep _ -> false
    | Nil -> true

  let fold_right_digit n ~init ~f = match n with
    | One (_, a) -> f a init
    | Two (_, a, b) -> f a @@ f b init
    | Three (_, a, b, c) -> f a @@ f b @@ f c init
    | Four (_, a, b, c, d) -> f a @@ f b @@ f c @@ f d init
  [@@specialise]

  let fold_left_digit n ~init ~f = match n with
    | One (_, a) -> f init a
    | Two (_, a, b) -> f (f init a) b
    | Three (_, a, b, c) -> f (f (f init a) b) c
    | Four (_, a, b, c, d) -> f (f (f (f init a) b) c) d
  [@@specialise]

  let fold_right_node n ~init ~f = match n with
    | Node2 (_, a, b) -> f a @@ f b init
    | Node3 (_, a, b, c) -> f a @@ f b @@ f c init
  [@@specialise]

  let fold_left_node n ~init ~f = match n with
    | Node2 (_, a, b) -> f (f init a) b
    | Node3 (_, a, b, c) -> f (f (f init a) b) c
  [@@specialise]

  let rec fold_right : 'acc 'a 'm.
    ('a, 'm) t ->
    init:'acc ->
    f:('a -> 'acc -> 'acc) ->
    'acc = fun t ~init ~f -> match t with
    | Nil -> init
    | Single x -> f x init
    | Deep (_, pr, m, sf) ->
      let init = fold_right_digit sf ~init ~f in
      let init = fold_right m ~init ~f:(fun n init ->
          fold_right_node n ~init ~f) in
      fold_right_digit pr ~init ~f
  [@@specialise]

  let rec fold_left : 'acc 'a 'm.
    ('a, 'm) t ->
    init:'acc ->
    f:('acc -> 'a -> 'acc) ->
    'acc = fun t ~init ~f -> match t with
    | Nil -> init
    | Single x -> f init x
    | Deep (_, pr, m, sf) ->
      let init = fold_left_digit pr ~init ~f in
      let init = fold_left m ~init ~f:(fun init n ->
          fold_left_node n ~init ~f) in
      fold_left_digit sf ~init ~f
  [@@specialise]

  let fold = fold_left

  type ('w, 'a, 'm) wrap = monoid:'m monoid -> measure:('a -> 'm) -> 'w

  let measure_digit = function
    | One (v, _)
    | Two (v, _, _)
    | Three (v, _, _, _)
    | Four (v, _, _, _, _) -> v

  let measure_node = function
    | Node2 (v, _, _)
    | Node3 (v, _, _, _) -> v

  let measure_t_node ~monoid = function
    | Nil -> monoid.zero
    | Single x -> measure_node x
    | Deep (v, _, _, _) -> v

  let measure_t ~monoid ~measure = function
    | Nil -> monoid.zero
    | Single x -> measure x
    | Deep (v, _, _, _) -> v
  [@@specialise]

  let one ~measure a = One (measure a, a) [@@specialise]
  let one_node a = One (measure_node a, a)

  let two ~monoid ~measure a b =
    Two (monoid.combine (measure a) (measure b), a, b)
  [@@specialise]

  let two_node ~monoid a b =
    Two (monoid.combine (measure_node a) (measure_node b), a, b)
  [@@specialise]

  let three ~monoid ~measure a b c =
    Three (monoid.combine
             (monoid.combine (measure a) (measure b))
             (measure c),
           a, b, c)
  [@@specialise]

  let three_node ~monoid a b c =
    Three (monoid.combine
             (monoid.combine (measure_node a) (measure_node b))
             (measure_node c),
           a, b, c)
  [@@specialise]

  let four ~monoid ~measure a b c d =
    Four (monoid.combine
            (monoid.combine (measure a) (measure b))
            (monoid.combine (measure c) (measure d)),
          a, b, c, d)
  [@@specialise]

  let four_node ~monoid a b c d =
    Four (monoid.combine
            (monoid.combine (measure_node a) (measure_node b))
            (monoid.combine (measure_node c) (measure_node d)),
          a, b, c, d)
  [@@specialise]

  let node2 ~monoid ~measure a b =
    Node2 (monoid.combine (measure a) (measure b), a, b)
  [@@specialise]

  let node2_node ~monoid a b =
    Node2 (monoid.combine (measure_node a) (measure_node b), a, b)
  [@@specialise]

  let node3 ~monoid ~measure a b c =
    Node3 (monoid.combine (measure a) @@
           monoid.combine (measure b) (measure c),
           a, b, c)
  [@@specialise]

  let node3_node ~monoid a b c =
    Node3 (monoid.combine (measure_node a) @@
           monoid.combine (measure_node b) (measure_node c),
           a, b, c)
  [@@specialise]

  let deep ~monoid pr m sf =
    let v = measure_digit pr in
    let v = monoid.combine v @@ measure_t_node ~monoid m in
    let v = monoid.combine v @@ measure_digit sf in
    Deep (v, pr, m, sf)
  [@@specialise]

  let cons_digit ~monoid ~measure d x = match d with
    | One (v, a) -> Two (monoid.combine (measure x) v, x, a)
    | Two (v, a, b) -> Three (monoid.combine (measure x) v, x, a, b)
    | Three (v, a, b, c) -> Four (monoid.combine (measure x) v, x, a, b, c)
    | Four _ -> assert false
  [@@specialise]

  let cons_digit_node ~monoid d x = match d with
    | One (v, a) -> Two (monoid.combine (measure_node x) v, x, a)
    | Two (v, a, b) -> Three (monoid.combine (measure_node x) v, x, a, b)
    | Three (v, a, b, c) ->
      Four (monoid.combine (measure_node x) v, x, a, b, c)
    | Four _ -> assert false
  [@@specialise]

  let snoc_digit ~monoid ~measure d x = match d with
    | One (v, a) -> Two (monoid.combine v (measure x), a, x)
    | Two (v, a, b) -> Three (monoid.combine v (measure x), a, b, x)
    | Three (v, a, b, c) -> Four (monoid.combine v (measure x), a, b, c, x)
    | Four _ -> assert false
  [@@specialise]

  let snoc_digit_node ~monoid d x = match d with
    | One (v, a) -> Two (monoid.combine v (measure_node x), a, x)
    | Two (v, a, b) -> Three (monoid.combine v (measure_node x), a, b, x)
    | Three (v, a, b, c) ->
      Four (monoid.combine v (measure_node x), a, b, c, x)
    | Four _ -> assert false
  [@@specialise]

  let rec cons_aux : 'a 'm.
    monoid:'m monoid ->
    (('a, 'm) node, 'm) t ->
    ('a, 'm) node ->
    (('a, 'm) node, 'm) t = fun ~monoid t a -> match t with
    | Nil -> Single a
    | Single b -> deep ~monoid (one_node a) Nil (one_node b)
    | Deep (_, Four (_, b, c, d, e), m, sf) ->
      deep ~monoid
        (two_node ~monoid a b)
        (cons_aux ~monoid m @@ node3_node ~monoid c d e)
        sf
    | Deep (v, pr, m, sf) ->
      Deep (monoid.combine (measure_node a) v,
            cons_digit_node ~monoid pr a,
            m, sf)
  [@@specialise]

  let cons ~monoid ~measure t a = match t with
    | Nil -> Single a
    | Single b -> deep ~monoid (one ~measure a) Nil (one ~measure b)
    | Deep (_, Four (_, b, c, d, e), m, sf) ->
      deep ~monoid
        (two ~monoid ~measure a b)
        (cons_aux ~monoid m @@ node3 ~monoid ~measure c d e)
        sf
    | Deep (v, pr, m, sf) ->
      Deep (monoid.combine (measure a) v,
            cons_digit ~monoid ~measure pr a,
            m, sf)
  [@@specialise]

  let rec snoc_aux : 'a 'm.
    monoid:'m monoid ->
    (('a, 'm) node, 'm) t ->
    ('a, 'm) node ->
    (('a, 'm) node, 'm) t = fun ~monoid t a -> match t with
    | Nil -> Single a
    | Single b -> deep ~monoid (one_node b) Nil (one_node a)
    | Deep (_, pr, m, Four (_, b, c, d, e)) ->
      deep ~monoid pr
        (snoc_aux ~monoid m @@ node3_node ~monoid b c d)
        (two_node ~monoid e a)
    | Deep (v, pr, m, sf) ->
      Deep (monoid.combine v @@ measure_node a,
            pr, m,
            snoc_digit_node ~monoid sf a)
  [@@specialise]

  let snoc ~monoid ~measure t a = match t with
    | Nil -> Single a
    | Single b -> deep ~monoid (one ~measure b) Nil (one ~measure a)
    | Deep (_, pr, m, Four (_, b, c, d, e)) ->
      deep ~monoid pr
        (snoc_aux ~monoid m @@ node3 ~monoid ~measure b c d)
        (two ~measure ~monoid e a)
    | Deep (v, pr, m, sf) ->
      Deep (monoid.combine v @@ measure a,
            pr, m,
            snoc_digit ~monoid ~measure sf a)
  [@@specialise]

  let to_tree_digit_node ~monoid = function
    | One (_, a) -> Single a
    | Two (v, a, b) -> Deep (v, one_node a, Nil, one_node b)
    | Three (v, a, b, c) -> Deep (v, two_node ~monoid a b, Nil, one_node c)
    | Four (v, a, b, c, d) -> Deep (v, three_node ~monoid a b c, Nil, one_node d)
  [@@specialise]

  let to_tree_digit ~monoid ~measure = function
    | One (_, a) -> Single a
    | Two (v, a, b) -> Deep (v, one ~measure a, Nil, one ~measure b)
    | Three (v, a, b, c) ->
      Deep (v, two ~monoid ~measure a b, Nil, one ~measure c)
    | Four (v, a, b, c, d) ->
      Deep (v, three ~monoid ~measure a b c, Nil, one ~measure d)
  [@@specialise]

  let to_tree_list ~monoid ~measure = function
    | [] -> Nil
    | [a] -> Single a
    | [a; b] -> deep ~monoid (one ~measure a) Nil (one ~measure b)
    | [a; b; c] -> deep ~monoid (two ~monoid ~measure a b) Nil (one ~measure c)
    | [a; b; c; d] ->
      deep ~monoid (three ~monoid ~measure a b c) Nil (one ~measure d)
    | _ -> assert false
  [@@specialise]

  let to_digit_node = function
    | Node2 (v, a, b) -> Two (v, a, b)
    | Node3 (v, a, b, c) -> Three (v, a, b, c)

  let to_digit_list ~monoid ~measure = function
    | [a] -> one ~measure a
    | [a; b] -> two ~monoid ~measure a b
    | [a; b; c] -> three ~monoid ~measure a b c
    | [a; b; c; d] -> four ~monoid ~measure a b c d
    | _ -> assert false
  [@@specialise]

  let to_digit_list_node ~monoid = function
    | [a] -> one_node a
    | [a; b] -> two_node ~monoid a b
    | [a; b; c] -> three_node ~monoid a b c
    | [a; b; c; d] -> four_node ~monoid a b c d
    | _ -> assert false
  [@@specialise]

  let head_digit = function
    | One (_, a)
    | Two (_, a, _)
    | Three (_, a, _, _)
    | Four (_, a, _, _, _) -> a

  let last_digit = function
    | One (_, a)
    | Two (_, _, a)
    | Three (_, _, _, a)
    | Four (_, _, _, _, a) -> a

  let tail_digit_node ~monoid = function
    | One _ -> assert false
    | Two (_, _, a) -> one_node a
    | Three (_, _, a, b) -> two_node ~monoid a b
    | Four (_, _, a, b, c) -> three_node ~monoid a b c
  [@@specialise]

  let tail_digit ~monoid ~measure = function
    | One _ -> assert false
    | Two (_, _, a) -> one ~measure a
    | Three (_, _, a, b) -> two ~monoid ~measure a b
    | Four (_, _, a, b, c) -> three ~monoid ~measure a b c
  [@@specialise]

  let init_digit_node ~monoid = function
    | One _ -> assert false
    | Two (_, a, _) -> one_node a
    | Three (_, a, b, _) -> two_node ~monoid a b
    | Four (_, a, b, c, _) -> three_node ~monoid a b c
  [@@specialise]

  let init_digit ~monoid ~measure = function
    | One _ -> assert false
    | Two (_, a, _) -> one ~measure a
    | Three (_, a, b, _) -> two ~monoid ~measure a b
    | Four (_, a, b, c, _) -> three ~monoid ~measure a b c
  [@@specialise]

  type ('a, 'rest) view =
    | Vnil
    | Vcons of 'a * 'rest

  let rec view_left_aux : 'a 'm.
    monoid:'m monoid ->
    (('a, 'm) node, 'm) t ->
    (('a, 'm) node, (('a, 'm) node, 'm) t) view = fun ~monoid -> function
    | Nil -> Vnil
    | Single x -> Vcons (x, Nil)
    | Deep (_, One (_, a), m, sf) ->
      let vcons = match view_left_aux ~monoid m with
        | Vnil -> to_tree_digit_node ~monoid sf
        | Vcons (a, m') -> deep ~monoid (to_digit_node a) m' sf in
      Vcons (a, vcons)
    | Deep (_, pr, m, sf) ->
      let vcons = deep ~monoid (tail_digit_node ~monoid pr) m sf in
      Vcons (head_digit pr, vcons)
  [@@specialise]

  let view_left ~monoid ~measure = function
    | Nil -> Vnil
    | Single x -> Vcons (x, Nil)
    | Deep (_, One (_, a), m, sf) ->
      let vcons = match view_left_aux ~monoid m with
        | Vnil -> to_tree_digit ~monoid ~measure sf
        | Vcons (a, m') -> deep ~monoid (to_digit_node a) m' sf in
      Vcons (a, vcons)
    | Deep (_, pr, m, sf) ->
      let vcons = deep ~monoid (tail_digit ~monoid ~measure pr) m sf in
      Vcons (head_digit pr, vcons)
  [@@specialise]

  let rec view_right_aux : 'a 'm.
    monoid:'m monoid ->
    (('a, 'm) node, 'm) t ->
    (('a, 'm) node, (('a, 'm) node, 'm) t) view = fun ~monoid -> function
    | Nil -> Vnil
    | Single x -> Vcons (x, Nil)
    | Deep (_, pr, m, One (_, a)) ->
      let vcons = match view_right_aux ~monoid m with
        | Vnil -> to_tree_digit_node ~monoid pr
        | Vcons (a, m') -> deep ~monoid pr m' @@ to_digit_node a in
      Vcons (a, vcons)
    | Deep (_, pr, m, sf) ->
      let vcons = deep ~monoid pr m @@ init_digit_node ~monoid sf in
      Vcons (last_digit sf, vcons)
  [@@specialise]

  let view_right ~monoid ~measure = function
    | Nil -> Vnil
    | Single x -> Vcons (x, Nil)
    | Deep (_, pr, m, One (_, a)) ->
      let vcons = match view_right_aux ~monoid m with
        | Vnil -> to_tree_digit ~monoid ~measure pr
        | Vcons (a, m') -> deep ~monoid pr m' @@ to_digit_node a in
      Vcons (a, vcons)
    | Deep (_, pr, m, sf) ->
      let vcons = deep ~monoid pr m @@ init_digit ~monoid ~measure sf in
      Vcons (last_digit sf, vcons)
  [@@specialise]

  let rec find t ~f ~monoid ~measure =
    match view_left t ~monoid ~measure with
    | Vnil -> None
    | Vcons (x, _) when f x -> Some x
    | Vcons (_, t) -> find t ~f ~monoid ~measure
  [@@specialise]

  let findi t ~f ~monoid ~measure =
    let rec aux t i ~f ~monoid ~measure =
      match view_left t ~monoid ~measure with
      | Vnil -> None
      | Vcons (x, _) when f i x -> Some (i, x)
      | Vcons (_, t) -> aux t (i + 1) ~f ~monoid ~measure in
    aux t 0 ~f ~monoid ~measure
  [@@specialise]

  let rec exists t ~f ~monoid ~measure =
    match view_left t ~monoid ~measure with
    | Vnil -> false
    | Vcons (x, t) -> f x || exists t ~f ~monoid ~measure
  [@@specialise]

  let rec to_sequence t ~monoid ~measure =
    let open Seq.Generator in
    let rec aux t ~monoid ~measure =
      match view_left t ~monoid ~measure with
      | Vnil -> return ()
      | Vcons (x, t) ->
        yield x >>= fun () -> aux t ~monoid ~measure in
    run @@ aux t ~monoid ~measure
  [@@specialise]

  let rec to_sequence_rev t ~monoid ~measure =
    let open Seq.Generator in
    let rec aux t ~monoid ~measure =
      match view_right t ~monoid ~measure with
      | Vnil -> return ()
      | Vcons (x, t) ->
        yield x >>= fun () -> aux t ~monoid ~measure in
    run @@ aux t ~monoid ~measure
  [@@specialise]

  let head_exn = function
    | Nil -> invalid_arg "head_exn: Nil"
    | Single a -> a
    | Deep (_, pr, _, _) -> head_digit pr

  let head = function
    | Nil -> None
    | Single a -> Some a
    | Deep (_, pr, _, _) -> Some (head_digit pr)

  let last_exn = function
    | Nil -> invalid_arg "last_exn: Nil"
    | Single a -> a
    | Deep (_, _, _, sf) -> last_digit sf

  let last = function
    | Nil -> None
    | Single a -> Some a
    | Deep (_, _, _, sf) -> Some (last_digit sf)

  let tail_exn ~monoid ~measure t = match view_left ~monoid ~measure t with
    | Vnil -> invalid_arg "tail_exn: Vnil"
    | Vcons (_, tl) -> tl
  [@@specialise]

  let tail ~monoid ~measure t = match view_left ~monoid ~measure t with
    | Vcons (_, tl) -> Some tl
    | Vnil -> None
  [@@specialise]

  let front_exn ~monoid ~measure t = match view_left ~monoid ~measure t with
    | Vnil -> invalid_arg "front_exn: Vnil"
    | Vcons (hd, tl) -> tl, hd
  [@@specialise]

  let front ~monoid ~measure t = match view_left ~monoid ~measure t with
    | Vcons (hd, tl) -> Some (tl, hd)
    | Vnil -> None
  [@@specialise]

  let init_exn ~monoid ~measure t = match view_right ~monoid ~measure t with
    | Vnil -> invalid_arg "init_exn: Vnil"
    | Vcons (_, tl) -> tl
  [@@specialise]

  let init ~monoid ~measure t = match view_right ~monoid ~measure t with
    | Vcons (_, tl) -> Some tl
    | Vnil -> None
  [@@specialise]

  let rear_exn ~monoid ~measure t = match view_right ~monoid ~measure t with
    | Vnil -> invalid_arg "rear_exn: Vnil"
    | Vcons (hd, tl) -> tl, hd
  [@@specialise]

  let rear ~monoid ~measure t = match view_right ~monoid ~measure t with
    | Vcons (hd, tl) -> Some (tl, hd)
    | Vnil -> None
  [@@specialise]

  let add_digit_to digit l = match digit with
    | One (_, a) -> a :: l
    | Two (_, a, b) -> a :: b :: l
    | Three (_, a, b, c) -> a :: b :: c :: l
    | Four (_, a, b, c, d) -> a :: b :: c :: d :: l

  let rec nodes_aux ~monoid ~measure ts sf2 = match ts, sf2 with
    | [], One _ -> assert false
    | [], Two (_, a, b)
    | [a], One (_, b) -> [node2 ~monoid ~measure a b]
    | [], Three (_, a, b, c)
    | [a], Two (_, b, c)
    | [a; b], One (_, c) -> [node3 ~monoid ~measure a b c]
    | [], Four (_, a, b, c, d)
    | [a], Three (_, b, c, d)
    | [a; b], Two (_, c, d)
    | [a; b; c], One (_, d) ->
      [node2 ~monoid ~measure a b; node2 ~monoid ~measure c d]
    | a :: b :: c :: ts, _ ->
      node3 ~monoid ~measure a b c :: nodes_aux ~monoid ~measure ts sf2
    | [a], Four (_, b, c, d, e)
    | [a; b], Three (_, c, d, e) ->
      [node3 ~monoid ~measure a b c; node2 ~monoid ~measure d e]
    | [a; b], Four (_, c, d, e, f) ->
      [node3 ~monoid ~measure a b c; node3 ~monoid ~measure d e f]
  [@@specialise]

  let nodes ~monoid ~measure sf1 ts sf2 =
    nodes_aux ~monoid ~measure (add_digit_to sf1 ts) sf2
  [@@specialise]

  let rec app3 : 'a 'm.
    monoid:'m monoid ->
    measure:('a -> 'm) ->
    ('a, 'm) t ->
    'a list ->
    ('a, 'm) t ->
    ('a, 'm) t = fun ~monoid ~measure t1 elts t2 ->
    match t1, t2 with
    | Nil, _ ->
      List.fold_right elts ~f:(fun elt acc ->
          cons ~monoid ~measure acc elt) ~init:t2
    | _, Nil ->
      List.fold_left elts ~init:t1 ~f:(fun acc elt ->
          snoc ~monoid ~measure acc elt)
    | Single x1, _ ->
      cons ~monoid ~measure
        (List.fold_right elts ~init:t2 ~f:(fun elt acc ->
             cons ~monoid ~measure acc elt))
        x1
    | _, Single x2 ->
      snoc ~monoid ~measure
        (List.fold_left elts ~init:t1 ~f:(fun acc elt ->
             snoc ~monoid ~measure acc elt))
        x2
    | Deep (_, pr1, m1, sf1), Deep (_, pr2, m2, sf2) ->
      deep ~monoid pr1
        (app3 ~monoid ~measure:measure_node m1
           (nodes ~monoid ~measure sf1 elts pr2)
           m2)
        sf2
  [@@specialise]

  let append ~monoid ~measure t1 t2 = app3 ~monoid ~measure t1 [] t2
  [@@specialise]

  let reverse_digit_node ~monoid rev_a = function
    | One (_, a) -> one_node @@ rev_a a
    | Two (_, a, b) -> two_node ~monoid (rev_a b) (rev_a a)
    | Three (_, a, b, c) -> three_node ~monoid (rev_a c) (rev_a b) (rev_a a)
    | Four (_, a, b, c, d) ->
      four_node ~monoid (rev_a d) (rev_a c) (rev_a b) (rev_a a)
  [@@specialise]

  let reverse_digit ~monoid ~measure = function
    | One _ as d -> d
    | Two (_, a, b) -> two ~monoid ~measure b a
    | Three (_, a, b, c) -> three ~monoid ~measure c b a
    | Four (_, a, b, c, d) -> four ~monoid ~measure d c b a
  [@@specialise]

  let reverse_node_node ~monoid rev_a = function
    | Node2 (_, a, b) -> node2_node ~monoid (rev_a b) (rev_a a)
    | Node3 (_, a, b, c) -> node3_node ~monoid (rev_a c) (rev_a b) (rev_a a)
  [@@specialise]

  let reverse_node ~monoid ~measure = function
    | Node2 (_, a, b) -> node2 ~monoid ~measure b a
    | Node3 (_, a, b, c) -> node3 ~monoid ~measure c b a
  [@@specialise]

  let rec reverse_aux : 'a 'm.
    monoid:'m monoid ->
    (('a, 'm) node -> ('a, 'm) node) ->
    (('a, 'm) node, 'm) t ->
    (('a, 'm) node, 'm) t = fun ~monoid rev_a -> function
    | Nil -> Nil
    | Single a -> Single (rev_a a)
    | Deep (_, pr, m, sf) ->
      let rev_pr = reverse_digit_node ~monoid rev_a pr in
      let rev_sf = reverse_digit_node ~monoid rev_a sf in
      let rev_m = reverse_aux ~monoid (reverse_node_node ~monoid rev_a) m in
      deep ~monoid rev_sf rev_m rev_pr
  [@@specialise]

  let reverse ~monoid ~measure = function
    | Nil | Single _ as t -> t
    | Deep (_, pr, m, sf) ->
      let rev_pr = reverse_digit ~monoid ~measure pr in
      let rev_sf = reverse_digit ~monoid ~measure sf in
      let rev_m = reverse_aux ~monoid (reverse_node ~monoid ~measure) m in
      deep ~monoid rev_sf rev_m rev_pr
  [@@specialise]

  type ('a, 'rest) split = Split of 'rest * 'a * 'rest

  let split_digit ~monoid ~measure p i = function
    | One (_, a) -> Split ([], a, [])
    | Two (_, a, b) when p @@ monoid.combine i @@ measure a ->
      Split ([], a, [b])
    | Two (_, a, b) -> Split ([a], b, [])
    | Three (_, a, b, c) ->
      let i' = monoid.combine i @@ measure a in
      if p i' then Split ([], a, [b; c]) else
        let i'' = monoid.combine i' @@ measure b in
        if p i'' then Split ([a], b, [c])
        else Split ([a; b], c, [])
    | Four (_, a, b, c, d) ->
      let i' = monoid.combine i @@ measure a in
      if p i' then Split ([], a, [b; c; d]) else
        let i'' = monoid.combine i' @@ measure b in
        if p i'' then Split ([a], b, [c; d]) else
          let i''' = monoid.combine i'' @@ measure c in
          if p i''' then Split ([a; b], c, [d])
          else Split ([a; b; c;], d, [])
  [@@specialise]

  let deep_left ~monoid ~measure pr m sf =
    if List.is_empty pr then
      match view_left ~monoid ~measure:measure_node m with
      | Vnil -> to_tree_digit ~monoid ~measure sf
      | Vcons (a, m') -> deep ~monoid (to_digit_node a) m' sf
    else deep ~monoid (to_digit_list ~monoid ~measure pr) m sf
  [@@specialise]

  let deep_right ~monoid ~measure pr m sf =
    if List.is_empty sf then
      match view_right ~monoid ~measure:measure_node m with
      | Vnil -> to_tree_digit ~monoid ~measure pr
      | Vcons (a, m') -> deep ~monoid pr m' @@ to_digit_node a
    else deep ~monoid pr m @@ to_digit_list ~monoid ~measure sf
  [@@specialise]

  let rec split_tree : 'a 'm.
    monoid:'m monoid ->
    measure:('a -> 'm) ->
    ('m -> bool) ->
    'm ->
    ('a, 'm) t ->
    ('a, ('a, 'm) t) split = fun ~monoid ~measure p i -> function
    | Nil -> invalid_arg "split_tree: Nil"
    | Single x -> Split (Nil, x, Nil)
    | Deep (_, pr, m, sf) ->
      let vpr = monoid.combine i @@ measure_digit pr in
      if p vpr then
        let Split (l, x, r) = split_digit ~monoid ~measure p i pr in
        Split (to_tree_list ~monoid ~measure l,
               x,
               deep_left ~monoid ~measure r m sf)
      else
        let vm = monoid.combine vpr @@ measure_t_node ~monoid m in
        if p vm then
          let Split (ml, xs, mr) =
            split_tree ~monoid ~measure:measure_node p vpr m in
          let Split (l, x, r) =
            split_digit ~monoid ~measure p
              (monoid.combine vpr (measure_t_node ~monoid ml))
              (to_digit_node xs) in
          Split (deep_right ~monoid ~measure pr ml l,
                 x,
                 deep_left ~monoid ~measure r mr sf)
        else
          let Split (l, x, r) = split_digit ~monoid ~measure p vm sf in
          Split (deep_right ~monoid ~measure pr m l,
                 x,
                 to_tree_list ~monoid ~measure r)
  [@@specialise]

  let split ~monoid ~measure ~f = function
    | Nil -> Nil, Nil
    | t when f @@ measure_t ~monoid ~measure t ->
      let Split (l, x, r) = split_tree ~monoid ~measure f monoid.zero t in
      l, cons ~monoid ~measure r x
    | t -> t, Nil
  [@@specialise]

  let lookup_digit ~monoid ~measure p i = function
    | One (_, a) -> monoid.zero, a
    | Two (_, a, b) ->
      let ma = measure a in
      let i' = monoid.combine i ma in
      if p i' then monoid.zero, a else ma, b
    | Three (_, a, b, c) ->
      let ma = measure a in
      let i' = monoid.combine i ma in
      if p i' then monoid.zero, a else
        let mb = measure b in
        let i'' = monoid.combine i' mb in
        if p i'' then ma, b else monoid.combine ma mb, c
    | Four (_, a, b, c, d) ->
      let ma = measure a in
      let i' = monoid.combine i ma in
      if p i' then monoid.zero, a else
        let mb = measure b in
        let i'' = monoid.combine i' mb in
        if p i'' then ma, b else
          let mc = measure c in
          let i''' = monoid.combine i'' mc in
          if p i''' then monoid.combine ma mb, c
          else monoid.combine (monoid.combine ma mb) mc, d
  [@@specialise]

  let lookup_node ~monoid ~measure p i = function
    | Node2 (_, a, b) ->
      let ma = measure a in
      let i' = monoid.combine i ma in
      if p i' then monoid.zero, a else ma, b
    | Node3 (_, a, b, c) ->
      let ma = measure a in
      let i' = monoid.combine i ma in
      if p i' then monoid.zero, a else
        let mb = measure b in
        let i'' = monoid.combine i' mb in
        if p i'' then ma, b else monoid.combine ma mb, c
  [@@specialise]

  let rec lookup_tree : 'a 'm.
    monoid:'m monoid ->
    measure:('a -> 'm) ->
    ('m -> bool) ->
    'm ->
    ('a, 'm) t ->
    'm * 'a = fun ~monoid ~measure p i -> function
    | Nil -> invalid_arg "lookup_tree: Nil"
    | Single x -> monoid.zero, x
    | Deep (_, pr, m, sf) ->
      let mpr = measure_digit pr in
      let vpr = monoid.combine i mpr in
      if p vpr then lookup_digit ~monoid ~measure p i pr else
        let mm = measure_t_node ~monoid m in
        let vm = monoid.combine vpr mm in
        if p vm then
          let vleft, node =
            lookup_tree ~monoid ~measure:measure_node p vpr m in
          let v, x =
            lookup_node ~monoid ~measure p
              (monoid.combine vpr vleft)
              node in
          monoid.combine (monoid.combine mpr vleft) v, x
        else
          let v, x = lookup_digit ~monoid ~measure p vm sf in
          monoid.combine (monoid.combine mpr mm) v, x
  [@@specialise]

  let lookup ~monoid ~measure p t =
    snd @@ lookup_tree ~monoid ~measure p monoid.zero t
  [@@specialise]

  type ('a, 'm) iter =
    | End
    | Next of 'a * ('a, 'm) iter
    | Digit of ('a, 'm) digit * ('a, 'm) iter
    | Fg of (('a, 'm) node, 'm) iter * ('a, 'm) iter

  let rec to_iter : 'a. ('a, 'm) t -> ('a, 'm) iter -> ('a, 'm) iter =
    fun t k -> match t with
      | Nil -> k
      | Single a -> Next (a, k)
      | Deep (_, pr, m, sf) -> Digit (pr, Fg (to_iter m End, Digit (sf, k)))

  let rec to_iter_rev : 'a. ('a, 'm) t -> ('a, 'm) iter -> ('a, 'm) iter =
    fun t k -> match t with
      | Nil -> k
      | Single a -> Next (a, k)
      | Deep (_, pr, m, sf) ->
        Digit (sf, Fg (to_iter_rev m End, Digit (pr, k)))

  let rec iter_next : 'a.
    ('a, 'm) iter ->
    ('a * ('a, 'm) iter) option = function
    | End -> None
    | Next (v, k) -> Some (v, k)
    | Digit (One (_, a), k) -> Some (a, k)
    | Digit (Two (_, a, b), k) -> Some (a, Next (b, k))
    | Digit (Three (_, a, b, c), k) -> Some (a, Next (b, Next (c, k)))
    | Digit (Four (_, a, b, c, d), k) ->
      Some (a, Next (b, Next (c, Next (d, k))))
    | Fg (i, k) -> match iter_next i with
      | None -> iter_next k
      | Some (Node2 (_, a, b), kn) -> Some (a, Next (b, Fg (kn, k)))
      | Some (Node3 (_, a, b, c), kn) ->
        Some (a, Next (b, Next (c, Fg (kn, k))))

  let rec iter_next_rev : 'a.
    ('a, 'm) iter ->
    ('a * ('a, 'm) iter) option = function
    | End -> None
    | Next (v, k) -> Some (v, k)
    | Digit (One (_, a), k) -> Some (a, k)
    | Digit (Two (_, a, b), k) -> Some (b, Next (a, k))
    | Digit (Three (_, a, b, c), k) -> Some (c, Next (b, Next (a, k)))
    | Digit (Four (_, a, b, c, d), k) ->
      Some (d, Next (c, Next (b, Next (a, k))))
    | Fg (i, k) -> match iter_next_rev i with
      | None -> iter_next_rev k
      | Some (Node2 (_, a, b), kn) -> Some (b, Next (a, Fg (kn, k)))
      | Some (Node3 (_, a, b, c), kn) ->
        Some (c, Next (b, Next (a, Fg (kn, k))))

  let of_list ~monoid ~measure =
    List.fold ~init:empty ~f:(snoc ~monoid ~measure)
  [@@specialise]

  let of_list_rev ~monoid ~measure =
    List.fold ~init:empty ~f:(cons ~monoid ~measure)
  [@@specialise]

  let iter t ~f = fold_left t ~init:() ~f:(fun () a -> f a)
  [@@specialise]

  let iter_rev t ~f = fold_right t ~init:() ~f:(fun a () -> f a)
  [@@specialise]

  let map ~monoid ~measure ~f =
    fold_left ~init:empty ~f:(fun acc a -> snoc ~monoid ~measure acc @@ f a)
  [@@specialise]

  let map_rev ~monoid ~measure ~f =
    fold_left ~init:empty ~f:(fun acc a -> cons ~monoid ~measure acc @@ f a)
  [@@specialise]

  let compare t1 t2 ~compare =
    let rec loop i1 i2 = match iter_next i1, iter_next i2 with
      | None, None -> 0
      | Some _, None -> 1
      | None, Some _ -> -1
      | Some (e1, i1), Some (e2, i2) ->
        let c = compare e1 e2 in
        if c <> 0 then c else loop i1 i2 in
    loop (to_iter t1 End) (to_iter t2 End)
  [@@specialise]

  let equal t1 t2 ~equal =
    let rec loop i1 i2 ~equal = match iter_next i1, iter_next i2 with
      | None, None -> true
      | Some _, None -> false
      | None, Some _ -> false
      | Some (e1, i1), Some (e2, i2) -> equal e1 e2 && loop i1 i2 ~equal in
    loop (to_iter t1 End) (to_iter t2 End) ~equal
  [@@specialise]
end

let monoid = {zero = 0; combine = (+)}
let measure _ = 1

type 'a t = ('a, int) Generic.t [@@deriving bin_io, sexp]

let compare = Generic.compare
let equal = Generic.equal
let last_exn = Generic.last_exn
let head_exn = Generic.head_exn
let last = Generic.last
let head = Generic.head
let singleton = Generic.singleton
let empty = Generic.empty
let is_empty = Generic.is_empty
let fold_left = Generic.fold_left
let fold = fold_left
let fold_right = Generic.fold_right
let iter = Generic.iter
let iter_rev = Generic.iter_rev
let map t ~f = Generic.map ~monoid ~measure ~f t
let map_rev t ~f = Generic.map_rev ~monoid ~measure ~f t
let of_list l = Generic.of_list ~monoid ~measure l
let of_list_rev l = Generic.of_list_rev ~monoid ~measure l
let cons t x = Generic.cons ~monoid ~measure t x
let snoc t x = Generic.snoc ~monoid ~measure t x
let rear t = Generic.rear ~monoid ~measure t
let front t = Generic.front ~monoid ~measure t
let tail t = Generic.tail ~monoid ~measure t
let init t = Generic.init ~monoid ~measure t
let front_exn t = Generic.front_exn ~monoid ~measure t
let tail_exn t = Generic.tail_exn ~monoid ~measure t
let init_exn t = Generic.init_exn ~monoid ~measure t
let rear_exn t = Generic.rear_exn ~monoid ~measure t
let reverse t = Generic.reverse ~monoid ~measure t
let split t ~f = Generic.split ~monoid ~measure ~f t
let length t = Generic.measure_t ~monoid ~measure t
let append t1 t2 = Generic.append ~monoid ~measure t1 t2
let to_sequence t = Generic.to_sequence ~monoid ~measure t
let to_sequence_rev t = Generic.to_sequence_rev ~monoid ~measure t
let find t ~f = Generic.find ~monoid ~measure t ~f
let findi t ~f = Generic.findi ~monoid ~measure t ~f
let exists t ~f = Generic.exists ~monoid ~measure t ~f

let split_at_exn t i =
  if i < 0 || i >= length t then
    invalid_argf "split_at_exn: index %d out of bounds" i ();
  split t ~f:(fun idx -> i < idx)

let split_at t i = Option.try_with @@ fun () -> split_at_exn t i
let lookup_exn t ~f = Generic.lookup ~monoid ~measure f t
let lookup t ~f = Option.try_with @@ fun () -> lookup_exn t ~f

let get_exn t i =
  if i < 0 || i >= length t then
    invalid_argf "get_exn: index %d out of bounds" i ();
  lookup_exn t ~f:(fun idx -> i < idx)

let get t i = Option.try_with @@ fun () -> get_exn t i

let set t i v =
  if i < 0 || i >= length t then
    invalid_argf "set: index %d out of bounds" i ();
  let l, r = split_at_exn t i in
  append (snoc l v) (tail_exn r)

let update t i ~f = set t i @@ f @@ get_exn t i

let insert t x i =
  if i > 0 then
    if i < length t then
      let l, r = split t ~f:(fun idx -> i < idx) in
      append (snoc l x) r
    else snoc t x
  else cons t x

let remove t i =
  if i >= 0 && i < length t then
    let l, r = split t ~f:(fun idx -> i < idx) in
    if is_empty r then l else append l @@ tail_exn r
  else t

let filter t ~f = fold t ~init:empty ~f:(fun acc a ->
    if f a then snoc acc a else acc)

let remove_if t ~f =
  if exists t ~f then filter t ~f:(Fn.non f) else t

let update_if t x ~f = match findi t ~f:(fun _ x -> f x) with
  | Some (i, _) -> set t i x
  | None -> t

let enum ?(rev = false) t =
  if rev then to_sequence_rev t else to_sequence t

let to_list t = fold_right t ~init:[] ~f:List.cons

let rec next_aux s ~f = match Seq.next s with
  | Some (x, xs) when f x -> Seq.hd xs
  | Some (_, xs) -> next_aux xs ~f
  | None -> None
[@@specialise]

let next t ~f = next_aux ~f @@ to_sequence t [@@specialise]
let prev t ~f = next_aux ~f @@ to_sequence_rev t [@@specialise]

let pp ppx sep ppf t =
  let i = ref 0 in
  let last = length t - 1 in
  iter t ~f:(fun x ->
      Format.fprintf ppf "%a" ppx x;
      if !i < last then sep ppf;
      incr i)
