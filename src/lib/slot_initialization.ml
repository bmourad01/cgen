open Core
open Regular.Std
open Graphlib.Std

module Slot = Virtual.Slot

type interval = {
  lo : int;
  hi : int;
} [@@deriving compare, sexp]

module Interval = struct
  type point = int [@@deriving compare, sexp]
  type t = interval [@@deriving compare, sexp]

  let lower t = t.lo
  let upper t = t.hi

  let pp ppf t = Format.fprintf ppf "[%d,%d]" t.lo t.hi

  let from_access off ty =
    let lo = Int64.to_int_exn off in
    let sz = Type.sizeof_basic ty / 8 in
    {lo; hi = lo + sz - 1}

  let extended t = {
    lo = t.lo - 1;
    hi = t.hi + 1;
  }
end

module Tree = Interval_tree.Make(Interval)

(* For each slot, we have a set of intervals corresponding to
   relative byte offsets that were initialized by a store. *)
type state = unit Tree.t Var.Map.t

let equal_state s1 s2 =
  Map.equal (fun t1 t2 ->
      Seq.equal (fun (i1, _) (i2, _) ->
          Interval.compare i1 i2 = 0)
        (Tree.to_sequence t1)
        (Tree.to_sequence t2))
    s1 s2

let empty_state : state = Var.Map.empty

(* Starting constraint has the entry block with no incoming
   initializations. *)
let init_constraints : state Label.Map.t =
  Label.Map.singleton Label.pseudoentry empty_state

(* Our top element, which is every slot having been initialized. *)
let top_state slots : state =
  Map.map slots ~f:(fun s ->
      let i = {lo = 0; hi = Slot.size s - 1} in
      Tree.singleton i ())

(* Coalesce `i` with any overlapping or adjacent intervals in `t`. *)
let normalize_add t i =
  let lo, hi, t =
    Interval.extended i |> Tree.intersections t |> Seq.map ~f:fst |>
    Seq.fold ~init:(i.lo, i.hi, t) ~f:(fun (lo, hi, t) i ->
        min lo i.lo, max hi i.hi, Tree.remove t i) in
  Tree.add t {lo; hi} ()

(* Intersect the intervals (and also normalize them). *)
let merge_tree t1 t2 =
  Tree.to_sequence t1 |> Seq.map ~f:fst |>
  Seq.fold ~init:Tree.empty ~f:(fun init i1 ->
      Tree.intersections t2 i1 |> Seq.map ~f:fst |>
      Seq.fold ~init ~f:(fun acc i2 ->
          let lo = max i1.lo i2.lo in
          let hi = min i1.hi i2.hi in
          if lo <= hi then normalize_add acc {lo; hi} else acc))

(* Since this is a "must" forward-flow analysis, incoming
   predecessor states must intersect. *)
let merge_state s1 s2 =
  Map.merge s1 s2 ~f:(fun ~key:_ -> function
      | `Both (t1, t2) -> Some (merge_tree t1 t2)
      | `Left _ | `Right _ -> None)

type solution = (Label.t, state) Solution.t

type t = {
  soln : solution;
  bad  : Label.Hash_set.t;
}

(* If the slot is not always initialized by the
   time we reach the load, then we have UB. *)
let is_uninitialized acc base off ty =
  match Map.find acc base with
  | None -> true
  | Some t ->
    let i = Interval.from_access off ty in
    not (Tree.dominates t i)

let transfer_store esc acc ptr ty (s : Scalars.state) =
  match Map.find s ptr with
  | Some Offset (base, off) ->
    (* If `base` ever escaped, then don't ever consider
       it initialized. *)
    if Hash_set.mem esc base then
      let () = Logs.debug (fun m ->
          m "%s: ignoring escaped slot %a%!"
            __FUNCTION__ Var.pp base) in
      acc
    else
      let i = Interval.from_access off ty in
      Map.update acc base ~f:(function
          | None -> Tree.singleton i ()
          | Some t when Tree.dominates t i -> t
          | Some t -> normalize_add t i)
  | _ -> acc

let transfer_load bad acc l ptr ty (s : Scalars.state) =
  match Map.find s ptr with
  | Some Offset (base, off) ->
    if is_uninitialized acc base off ty then
      Hash_set.add bad l;
    acc
  | _ -> acc

let debug_dump blks bad s =
  Logs.debug (fun m ->
      Label.Tree.iter blks ~f:(fun ~key ~data:_ ->
          let s = Solution.get s key in
          let pp_tree ppf (x, t) =
            Tree.to_sequence t |> Seq.to_list |>
            List.to_string ~f:(fun (i, ()) ->
                Format.asprintf "%a" Interval.pp i) |>
            Format.fprintf ppf "%a:%s" Var.pp x in
          m "%s: %a: incoming must-initialize: %s%!"
            __FUNCTION__ Label.pp key
            (Map.to_alist s |>
             List.to_string ~f:(Format.asprintf "%a" pp_tree))));
  Logs.debug (fun m ->
      Hash_set.iter bad ~f:(fun l ->
          m "%s: load at %a is potentially uninitialized%!"
            __FUNCTION__ Label.pp l))

module Make(M : Scalars.L) = struct
  open M

  module S = Scalars.Make(M)

  let transfer bad t blks slots l st =
    match Label.Tree.find blks l with
    | None -> st
    | Some b ->
      let s = ref @@ Scalars.get t l in
      Blk.insns b |> Seq.fold ~init:st ~f:(fun acc i ->
          let op = Insn.op i and l = Insn.label i in
          let acc = match Insn.load_or_store_to op with
            | Some (ptr, ty, Store) -> transfer_store t.esc acc ptr ty !s
            | Some (ptr, ty, Load) -> transfer_load bad acc l ptr ty !s
            | _ -> acc in
          s := S.transfer_op slots !s op;
          acc)

  let analyze' t cfg blks slots =
    let bad = Label.Hash_set.create () in
    let s = Graphlib.fixpoint (module Cfg) cfg
        ~init:(Solution.create init_constraints @@ top_state slots)
        ~start:Label.pseudoentry
        ~equal:equal_state
        ~merge:merge_state
        ~f:(transfer bad t blks slots) in
    debug_dump blks bad s;
    {soln = s; bad}

  let analyze cfg blks slots =
    let t = S.analyze cfg blks slots in
    analyze' t cfg blks slots
end
