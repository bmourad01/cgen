(* Performing instruction selection on a switch is limited to producing
   a single sequence of instructions (not multiple blocks), and so it can
   only do the naive lowering of the table it was given.

   This pass aims to do the more sophisticated lowering beforehand, so that
   we remove all the pathological cases that would result in isel trying to
   build giant or inefficient tables.

   The basic strategy is as follows:

   1. Coalesce same-target cases into (unsigned-sorted) range clusters.
   2. Group adjacent clusters into partitions.
   3. Each partition is either a range check, or an actual jump table,
      depending on our chosen "density" heuristics.
   4. Dispatch the partitions with a balanced decision tree, emitting
      non-leaf nodes as a `br` instruction to advance the "binary search".

   The resulting code has a worst case of O(log(n)) to actually dispatch to
   the correct switch case. So if the input switch was already dense, we still
   reap the benefits of the O(1) jump table lookup.

   This approach builds on the following papers:

   - "Producing good code for the case statement (1985)" by R.L. Bernstein
   - "Correction to 'producing good code for the case statement' (1994)" by
      S. Kannan, T.A. Proebsting
*)

open Core
open Virtual
open Context.Syntax

module Bv = Cgen_utils.Bv
module Vec = Cgen_containers.Vec
module Cva = Context.Virtual.Abi

let bty t = (t :> Type.basic)
let (.![]) = Vec.get_exn

(* A jump table is worthwhile only over a run of at least this many
   distinct targets ... *)
let min_jt_entries = 4

(* ... spanning no more than this many index values (bounding the emitted
   table), ... *)
let max_jt_span = 4096

(* ... and covering at least this fraction (1/4) of that span with real
   cases, so we never pad a mostly-empty table. *)
let density_num = 1
let density_den = 4

(* At most this many partitions are dispatched by a linear chain rather
   than a binary search. *)
let chain_max = 3

type cluster = {
  lo     : Bv.t;
  hi     : Bv.t;
  target : local;
}

let singleton v l = {lo = v; hi = v; target = l}
let cluster_count m c = Bv.to_int Bv.((c.hi - c.lo) mod m) + 1

let coalesce m cases =
  let acc = Vec.create () in
  match cases with
  | [] -> acc
  | (v, l) :: rest ->
    let init = singleton v l in
    let last = List.fold rest ~init ~f:(fun cur (v, l) ->
        let next = Bv.((succ cur.hi) mod m) in
        if Bv.(v = next) && equal_local l cur.target
        then {cur with hi = v}
        else (Vec.push acc cur; singleton v l)) in
    Vec.push acc last;
    acc

type partition =
  | Ptable of int * int
  | Prange of int

let part_lo cs = function
  | Ptable (i, _) -> cs.![i].lo
  | Prange i -> cs.![i].lo

let part_hi cs = function
  | Ptable (_, j) -> cs.![j].hi
  | Prange i -> cs.![i].hi

let partition m clusters =
  let n = Vec.length clusters in
  let parts = Vec.create ~capacity:n () in
  if n <> 0 then begin
    (* Prefix sums of per-cluster value counts, for O(1) window totals. *)
    let psum = Array.create ~len:(n + 1) 0 in
    for i = 0 to n - 1 do
      psum.(i + 1) <- psum.(i) + cluster_count m clusters.![i]
    done;
    let max_span = Bv.(int Int.(max_jt_span - 1) mod m) in
    (* Whether clusters [i..j] form an acceptable jump table. *)
    let can_jt i j =
      j - i + 1 >= min_jt_entries && begin
        let span = Bv.((clusters.![j].hi - clusters.![i].lo) mod m) in
        Bv.compare span max_span <= 0 && begin
          let span = Bv.to_int span + 1 in
          let values = psum.(j + 1) - psum.(i) in
          values * density_den >= span * density_num
        end
      end in
    let dp = Array.create ~len:(n + 1) 0 in
    (* `nxt.(i)` is the last cluster of the partition starting at `i`. *)
    let nxt = Array.create ~len:n 0 in
    for i = n - 1 downto 0 do
      dp.(i) <- 1 + dp.(i + 1);
      nxt.(i) <- i;
      for j = i + 1 to n - 1 do
        if can_jt i j && 1 + dp.(j + 1) < dp.(i) then begin
          dp.(i) <- 1 + dp.(j + 1);
          nxt.(i) <- j
        end
      done
    done;
    (* Follow the `nxt` chain from the start, emitting one partition per
       boundary (not one per cluster). *)
    let i = ref 0 in
    while !i < n do
      let j = nxt.(!i) in
      Vec.push parts (if j = !i then Prange !i else Ptable (!i, j));
      i := j + 1
    done
  end;
  parts

(* A jump table, defaulting to the miss target so it threads a chain.
   Its bounds check is left to isel. *)
let lower_switch m ty x miss i j clusters =
  let rec go c v acc =
    let acc = (v, c.target) :: acc in
    if Bv.(v = c.lo) then acc
    else go c Bv.(pred v mod m) acc in
  let cases = ref [] in
  for k = j downto i do
    let c = clusters.![k] in
    cases := go c c.hi !cases
  done;
  [], `sw (ty, `var x, miss, Abi.Ctrl.Table.create_exn !cases ty)

(* `lo` and `hi` are the current implied bounds of the index, so we can
   exploit that to elide the unsigned range check (either partially or
   completely) depending on the current partition. *)
let lower_range_check m lo hi ty x miss i clusters =
  let c = clusters.![i] in
  let tgt = (c.target :> dst) and miss = (miss :> dst) in
  match Bv.(c.lo = lo), Bv.(c.hi = hi) with
  | true, true ->
    !!([], `jmp tgt)
  | true, false ->
    let+ e, i = Cva.binop (`le (bty ty)) (`var x) (`int (c.hi, ty)) in
    [i], `br (e, tgt, miss)
  | false, true ->
    let+ e, i = Cva.binop (`ge (bty ty)) (`var x) (`int (c.lo, ty)) in
    [i], `br (e, tgt, miss)
  | false, false when Bv.(c.lo = c.hi) ->
    let+ e, i = Cva.binop (`eq (bty ty)) (`var x) (`int (c.lo, ty)) in
    [i], `br (e, tgt, miss)
  | false, false ->
    (* An unsigned range check `(x - lo) <=u (hi - lo)`. *)
    let span = Bv.((c.hi - c.lo) mod m) in
    let* s, isub = Cva.binop (`sub (bty ty)) (`var x) (`int (c.lo, ty)) in
    let+ e, ile = Cva.binop (`le (bty ty)) (`var s) (`int (span, ty)) in
    [isub; ile], `br (e, tgt, miss)

let lower_ctrl ty x default table =
  let m = Bv.modulus @@ Type.sizeof_imm ty in
  (* NB: `table` should be already sorted and deduplicated *)
  Abi.Ctrl.Table.enum table |>
  Sequence.filter ~f:(fun (_, l) -> not (equal_local l default)) |>
  Sequence.to_list |> function
  | [] -> !!([], `jmp (default :> dst), [])
  | cases ->
    let clusters = coalesce m cases in
    let parts = partition m clusters in
    let blocks = Vec.create () in
    let block (insns, ctrl) =
      let+ l = Context.Label.fresh in
      Vec.push blocks (Abi.Blk.create ~label:l ~insns ~ctrl ());
      `label (l, []) in
    let dispatch lo hi miss = function
      | Prange i -> lower_range_check m lo hi ty x miss i clusters
      | Ptable (i, j) -> !!(lower_switch m ty x miss i j clusters) in
    let rec chain lo hi lo_b hi_b =
      if lo = hi then dispatch lo_b hi_b default parts.![lo] else
        let p = parts.![lo] in
        (* If `p`'s lower bound was already known, a value reaching the next
           test must lie above `p`, so tighten the lower bound. *)
        let next_lo =
          if Bv.(part_lo clusters p = lo_b)
          then Bv.(succ (part_hi clusters p) mod m)
          else lo_b in
        let* next = chain (lo + 1) hi next_lo hi_b >>= block in
        dispatch lo_b hi_b next p
    and build lo hi lo_b hi_b =
      if hi - lo + 1 <= chain_max then chain lo hi lo_b hi_b else
        let mid = lo + (hi - lo + 1) / 2 in
        let pivot = part_lo clusters parts.![mid] in
        let* left = build lo (mid - 1) lo_b Bv.(pred pivot mod m) >>= block in
        let* right = build mid hi pivot hi_b >>= block in
        let+ e, cmp = Cva.binop (`lt (bty ty)) (`var x) (`int (pivot, ty)) in
        [cmp], `br (e, left, right) in
    let+ is, ctrl =
      build 0 (Vec.length parts - 1) Bv.zero Bv.(ones mod m) in
    is, ctrl, Vec.to_list blocks

let run fn =
  Abi.Func.blks fn |>
  Context.Seq.fold ~init:fn ~f:(fun fn blk ->
      match Abi.Blk.ctrl blk with
      | `sw (ty, i, default, table) ->
        let* x, pre = match i with
          | `var x -> !!(x, [])
          | `sym s ->
            let+ c, ci = Cva.unop (`copy (bty ty)) (`sym s) in
            c, [ci] in
        let+ is, ctrl, blks = lower_ctrl ty x default table in
        let blk = Abi.Blk.append_insns blk (pre @ is) in
        let blk = Abi.Blk.with_ctrl blk ctrl in
        List.fold blks
          ~init:(Abi.Func.update_blk fn blk)
          ~f:Abi.Func.insert_blk
      | _ -> !!fn)
