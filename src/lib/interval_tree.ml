(* Implementation borrowed from BAP *)

open Core
open Regular.Std
open Interval_tree_intf

module Make(I : Interval) = struct
  type key = I.t [@@deriving compare, sexp]
  type point = I.point [@@deriving compare, sexp]

  module P = Comparable.Make_plain(struct
      type t = point [@@deriving compare, sexp]
    end)

  type +'a node = {
    rhs      : 'a node option;
    lhs      : 'a node option;
    key      : key;
    data     : 'a;
    height   : int;
    greatest : point;
    least    : point;
  } [@@deriving fields, sexp]

  type +'a t = 'a node option [@@deriving sexp]

  let height = Option.value_map ~default:0 ~f:height
  let least = Option.map ~f:least
  let greatest = Option.map ~f:greatest
  let empty = None

  let bound f lhs top rhs =
    Option.merge lhs rhs ~f |>
    Option.value_map ~default:top ~f:(f top)

  let create lhs key data rhs =
    let hl = height lhs   and hr = height rhs in
    let mn = I.lower key  and mx = I.upper key in
    let ll = least lhs    and lr = least rhs in
    let gl = greatest lhs and gr = greatest rhs in
    Some {
      lhs; rhs; key; data;
      height = max hl hr + 1;
      least = bound P.min ll mn lr;
      greatest = bound P.max gl mx gr;
    }

  let singleton key data = create None key data None

  let rec min_binding = function
    | Some {lhs = None; key; data; _} -> Some (key, data)
    | Some {lhs; _} -> min_binding lhs
    | None -> None

  let rec max_binding = function
    | Some {rhs = None; key; data; _} -> Some (key, data)
    | Some {rhs; _} -> max_binding rhs
    | None -> None

  let bal l x d r =
    let hl, hr = height l, height r in
    if hl > hr + 2 then match l with
      | None -> assert false
      | Some t when height t.lhs >= height t.rhs ->
        create t.lhs t.key t.data (create t.rhs x d r)
      | Some t -> match t.rhs with
        | None -> assert false
        | Some rhs ->
          create (create t.lhs t.key t.data rhs.lhs)
            rhs.key rhs.data (create rhs.rhs x d r)
    else if hr > hl + 2 then match r with
      | None -> assert false
      | Some t when height t.rhs >= height t.lhs ->
        create (create l x d t.lhs) t.key t.data t.rhs
      | Some t -> match t.lhs with
        | None -> assert false
        | Some lhs ->
          create (create l x d lhs.lhs) lhs.key lhs.data
            (create lhs.rhs t.key t.data t.rhs)
    else create l x d r

  let rec add map key data = match map with
    | None -> singleton key data
    | Some t ->
      let c = I.compare key t.key in
      if c = 0 then bal map key data None
      else if c < 0
      then bal (add t.lhs key data) t.key t.data t.rhs
      else bal t.lhs t.key t.data (add t.rhs key data)

  let is_inside key p =
    let low = I.lower key and high = I.upper key in
    P.between ~low ~high p

  let lookup start a =
    let open Seq.Generator in
    let rec go = function
      | None -> return ()
      | Some t when P.(a < t.least || a > t.greatest) -> return ()
      | Some t ->
        if is_inside t.key a then
          go t.lhs >>= fun () ->
          yield (t.key, t.data) >>= fun () ->
          go t.rhs
        else
          go t.lhs >>= fun () ->
          go t.rhs in
    start |> go |> run

  let is_dominated t r =
    let open I in
    P.(lower r >= lower t.key && upper r <= upper t.key)

  let has_intersections t r =
    let open I in
    let open P in
    let p, q = lower t.key, upper t.key
    and x, y = lower r, upper r in
    if p <= x
    then x <= q && p <= y
    else p <= y && x <= q

  let can't_be_in_tree t r =
    let open I in
    P.(lower r > t.greatest || upper r < t.least)

  let can't_be_dominated t r =
    let open I in
    P.(lower r < t.least || upper r > t.greatest)

  let query ~skip_if ~take_if start r =
    let open Seq.Generator in
    let rec go = function
      | None -> return ()
      | Some t when skip_if t r -> return ()
      | Some t when take_if t r ->
        go t.lhs >>= fun () ->
        yield (t.key, t.data) >>= fun () ->
        go t.rhs
      | Some t ->
        go t.lhs >>= fun () ->
        go t.rhs in
    start |> go |> run

  let dominators m r = query m r
      ~skip_if:can't_be_dominated
      ~take_if:is_dominated

  let intersections m r = query m r
      ~skip_if:can't_be_in_tree
      ~take_if:has_intersections

  let dominates m r = not (Seq.is_empty (dominators m r))
  let intersects m r = not (Seq.is_empty (intersections m r))
  let contains m a = not (Seq.is_empty (lookup m a))

  let[@tail_mod_cons] rec map m ~f = match m with
    | None -> None
    | Some m -> Some {
        m with
        lhs = (map[@tailcall false]) m.lhs ~f;
        data = f m.data;
        rhs = (map[@tailcall]) m.rhs ~f;
      }

  let[@tail_mod_cons] rec mapi m ~f = match m with
    | None -> None
    | Some m -> Some {
        m with
        lhs = (mapi[@tailcall false]) m.lhs ~f;
        data = f m.key m.data;
        rhs = (mapi[@tailcall]) m.rhs ~f;
      }

  let rec remove_min_binding = function
    | Some {lhs = None; rhs; _} -> rhs
    | Some t -> bal (remove_min_binding t.lhs) t.key t.data t.rhs
    | None -> assert false

  let splice t1 t2 = match t1,t2 with
    | None, t | t, None -> t
    | _ -> match min_binding t2 with
      | Some (key, data) -> bal t1 key data (remove_min_binding t2)
      | None -> assert false

  let mem_equal x y =
    let open I in
    P.(lower x = lower y && upper x = upper y)

  let rec remove map mem = match map with
    | None -> None
    | Some t when mem_equal t.key mem ->
      splice (remove t.lhs mem) (remove t.rhs mem)
    | Some t -> match I.compare mem t.key with
      | 1 -> bal t.lhs t.key t.data (remove t.rhs mem)
      | _ -> bal (remove t.lhs mem) t.key t.data t.rhs

  let remove_if ~leave_if ~remove_if map mem =
    let rec remove = function
      | None -> None
      | Some t when leave_if t mem -> Some t
      | Some t when remove_if t mem ->
        splice (remove t.lhs) (remove t.rhs)
      | Some t ->
        bal (remove t.lhs) t.key t.data (remove t.rhs) in
    remove map

  let remove_intersections map mem = remove_if map mem
      ~leave_if:can't_be_in_tree
      ~remove_if:has_intersections

  let remove_dominators map mem = remove_if map mem
      ~leave_if:can't_be_dominated
      ~remove_if:is_dominated

  let filter_mapi map ~f =
    let rec fmap = function
      | None -> None
      | Some t -> match f t.key t.data with
        | None -> splice (fmap t.lhs) (fmap t.rhs)
        | Some data ->
          bal (fmap t.lhs) t.key data (fmap t.rhs) in
    fmap map

  let filter_map map ~f = filter_mapi map ~f:(fun _ x -> f x)
  let filter map ~f : _ t = filter_map map ~f:(fun x -> Option.some_if (f x) x)

  let to_sequence start =
    let open Seq.Generator in
    let rec go = function
      | None -> return ()
      | Some t ->
        go t.lhs >>= fun () ->
        yield (t.key, t.data) >>= fun () ->
        go t.rhs in
    start |> go |> run

  module C = Container.Make(struct
      type 'a t = 'a node option

      let rec fold m ~init ~f = Option.fold m ~init:init ~f:(fun acc m ->
          fold m.rhs ~init:(f (fold m.lhs ~init:acc ~f) m.data) ~f)

      let rec iter m ~f = Option.iter m ~f:(fun m ->
          iter m.lhs ~f;
          f m.data;
          iter m.rhs ~f)

      let iter  = `Custom iter
      let length = `Define_using_fold
    end)

  let fold = C.fold
  let count = C.count
  let sum = C.sum
  let iter = C.iter
  let length = C.length
  let is_empty = C.is_empty
  let exists = C.exists
  let mem = C.mem
  let for_all = C.for_all
  let find_map = C.find_map
  let find = C.find
  let to_list = C.to_list
  let to_array = C.to_array
  let min_elt = C.min_elt
  let max_elt = C.max_elt
  let fold_until = C.fold_until
  let fold_result = C.fold_result
end
