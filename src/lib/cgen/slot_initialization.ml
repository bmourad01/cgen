open Core
open Cgen_containers

module Slot = Virtual.Slot
module Vtree = Var.Tree
module VS = Var.Dense_set
module LS = Label.Dense_set
module LT = Label.Dense_table
module Solution = Fixpoint.Solution

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
type state = unit Tree.t Vtree.t

let equal_state s1 s2 =
  Vtree.equal (fun t1 t2 ->
      phys_equal t1 t2 ||
      Sequence.equal (fun (i1, _) (i2, _) ->
          Interval.compare i1 i2 = 0)
        (Tree.to_sequence t1)
        (Tree.to_sequence t2))
    s1 s2

let empty_state : state = Vtree.empty

(* Starting constraint has the entry block with no incoming
   initializations. *)
let init_constraints : state Label.Tree.t =
  Label.Tree.singleton Label.pseudoentry empty_state

(* Our top element, which is every slot having been initialized. *)
let top_state slots : state =
  Vtree.mapi slots ~f:(fun ~key:_ ~data:s ->
      let i = {lo = 0; hi = Slot.size s - 1} in
      Tree.singleton i ())

(* Coalesce `i` with any overlapping or adjacent intervals in `t`. *)
let normalize_add t i =
  let lo, hi, t =
    Tree.fold_intersections t (Interval.extended i) ~init:(i.lo, i.hi, t)
      ~f:(fun (lo, hi, t) j _ -> min lo j.lo, max hi j.hi, Tree.remove t j) in
  Tree.add t {lo; hi} ()

(* Intersect the intervals (and also normalize them). *)
let merge_tree t1 t2 =
  Tree.foldi t1 ~init:Tree.empty ~f:(fun init i1 () ->
      Tree.fold_intersections t2 i1 ~init ~f:(fun acc i2 () ->
          let lo = max i1.lo i2.lo in
          let hi = min i1.hi i2.hi in
          if lo <= hi then normalize_add acc {lo; hi} else acc))

(* Since this is a "must" forward-flow analysis, incoming
   predecessor states must intersect. *)
let merge_state s1 s2 =
  Vtree.inter_with s1 s2 ~f:(fun ~key:_ t1 t2 ->
      if phys_equal t1 t2 then t1 else merge_tree t1 t2)

type solution = state Solution.t

type t = {
  soln : solution;
  bad  : LS.t;
}

(* If the slot is not always initialized by the
   time we reach the load, then we have UB. *)
let is_uninitialized acc base off ty =
  match Vtree.find acc base with
  | None -> true
  | Some t ->
    let i = Interval.from_access off ty in
    not (Tree.dominates t i)

type access =
  | Load_at  of Var.t * int64 * Type.basic
  | Store_at of Var.t * int64 * Type.basic

let apply_store acc base off ty =
  let i = Interval.from_access off ty in
  Vtree.update_with acc base
    ~nil:(fun () -> Tree.singleton i ())
    ~has:(fun t ->
        if Tree.dominates t i then t
        else normalize_add t i)

let apply_load bad acc l base off ty =
  if is_uninitialized acc base off ty then LS.add bad l;
  acc

let debug_dump blks bad s =
  Logs.debug (fun m ->
      Label.Tree.iter blks ~f:(fun ~key ~data:_ ->
          let s = Solution.get s key in
          let pp_tree ppf (x, t) =
            Tree.to_sequence t |> Sequence.to_list |>
            List.to_string ~f:(fun (i, ()) ->
                Format.asprintf "%a" Interval.pp i) |>
            Format.fprintf ppf "%a:%s" Var.pp x in
          m "%s: %a: incoming must-initialize: %s%!"
            __FUNCTION__ Label.pp key
            (Vtree.to_list s |>
             List.to_string ~f:(Format.asprintf "%a" pp_tree))));
  Logs.debug (fun m ->
      LS.iter bad ~f:(fun l ->
          m "%s: load at %a is potentially uninitialized%!"
            __FUNCTION__ Label.pp l))

module Make(M : Scalars.L) = struct
  open M

  module S = Scalars.Make(M)

  let collect_accesses t blks slots =
    let ninsns =
      Label.Tree.fold blks ~init:0
        ~f:(fun ~key:_ ~data:b acc -> acc + Blk.num_insns b) in
    let accesses = LT.create ~capacity:ninsns () in
    Label.Tree.iter blks ~f:(fun ~key:l ~data:b ->
        let s = ref @@ Scalars.get t l in
        Blk.iter_insns b ~f:(fun i ->
            let op = Insn.op i in
            begin match Insn.load_or_store_to op with
              | Some (ptr, ty, kind) ->
                begin match Vtree.find !s ptr with
                  | Some Offset (base, off) ->
                    begin match kind with
                      | Load ->
                        LT.set accesses ~key:(Insn.label i)
                          ~data:(Load_at (base, off, ty))
                      | Store ->
                        (* An escaped slot is never considered initialized. *)
                        if VS.mem t.esc base then
                          Logs.debug (fun m ->
                              m "%s: ignoring escaped slot %a%!"
                                __FUNCTION__ Var.pp base)
                        else
                          LT.set accesses ~key:(Insn.label i)
                            ~data:(Store_at (base, off, ty))
                    end
                  | _ -> ()
                end
              | None -> ()
            end;
            s := S.transfer_op slots !s op));
    accesses

  let transfer bad accesses blks l st =
    match Label.Tree.find blks l with
    | None -> st
    | Some b ->
      Blk.fold_insns b ~init:st ~f:(fun acc i ->
          let l = Insn.label i in
          match LT.find accesses l with
          | Some (Store_at (base, off, ty)) ->
            apply_store acc base off ty
          | Some (Load_at (base, off, ty)) ->
            apply_load bad acc l base off ty
          | None -> acc)

  let analyze' t cfg blks slots =
    let bad = LS.create () in
    let accesses = collect_accesses t blks slots in
    let s = Fixpoint.run cfg
        ~init:(Solution.create init_constraints @@ top_state slots)
        ~start:Label.pseudoentry
        ~equal:equal_state
        ~merge:merge_state
        ~f:(transfer bad accesses blks) in
    debug_dump blks bad s;
    {soln = s; bad}

  let analyze cfg blks slots =
    let t = S.analyze cfg blks slots in
    analyze' t cfg blks slots
end
