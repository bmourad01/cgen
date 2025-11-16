open Core
open Regular.Std
open Graphlib.Std
open Scalars

module Slot = Virtual.Slot
module Allen = Allen_interval_algebra

let debug = false

type range = {
  lo : int;
  hi : int;
} [@@deriving compare, equal, sexp]

module Range = struct
  type t = range [@@deriving compare, equal, sexp]

  let pp ppf r = Format.fprintf ppf "[%d, %d]" r.lo r.hi

  let bad = {lo = Int.min_value; hi = Int.max_value}
  let is_bad = equal bad

  let singleton n = {lo = n; hi = n}

  (* Extend the upper-bound on the live range. *)
  let use r n = {r with hi = Int.max r.hi n}

  (* Shrink the lower-bound on the live range.

     Also, a defintion counts as a use, because we need to
     reference the slot, so extend the upper-bound.
  *)
  let def r n = {
    lo = Int.min r.lo n;
    hi = Int.max r.hi n;
  }

  module Algebra = Allen.Make(struct
      type point = int
      type nonrec t = t
      let lo t = t.lo [@@inline]
      let hi t = t.hi [@@inline]
      include Int.Replace_polymorphic_compare
    end)
end

let slot_sa slots x =
  let sx = Map.find_exn slots x in
  Slot.(size sx, align sx)

let compat_size_align slots x y =
  let sx, ax = slot_sa slots x in
  let sy, ay = slot_sa slots y in
  (* The smaller slot must not have a higher alignment. *)
  not ((sx < sy && ax > ay) || (sy < sx && ay > ax))

(* Find compatible slots. Most importantly, their live ranges must
   not interfere. *)
let equiv_range slots rs x y =
  compat_size_align slots x y &&
  let rx = Map.find_exn rs x in
  let ry = Map.find_exn rs y in
  let a : Allen.t = Range.Algebra.relate rx ry in
  if debug then
    Format.eprintf "%a, %a: %a\n%!"
      Var.pp x Var.pp y Sexp.pp (Allen.sexp_of_t a);
  match a with
  | Before | After -> true
  | _ -> false

let non_interfering slots rs =
  Map.to_sequence rs |>
  (* The results will still be correct if we omit this, but
     it is more efficient to just not consider them at all. *)
  Seq.filter ~f:(not @. Range.is_bad @. snd) |>
  Seq.map ~f:fst |>
  Var.Set.of_sequence |>
  Partition.trivial |>
  Partition.refine ~cmp:Var.compare ~equiv:(equiv_range slots rs)

(* invariant: a group is never empty *)
let canon_elt slots g =
  Group.enum g |> Seq.max_elt ~compare:(fun x y ->
      (* Assuming that the sizes and alignments are compatible,
         just pick the biggest one. *)
      let sx, ax = slot_sa slots x in
      let sy, ay = slot_sa slots y in
      match Int.compare sy sx with
      | 0 -> Int.compare ay ax
      | c -> c) |>
  Option.value_exn

let make_subst slots p =
  Partition.groups p |>
  Seq.fold ~init:Var.Map.empty ~f:(fun init g ->
      let canon = canon_elt slots g in
      Group.enum g |> Seq.filter ~f:(not @. Var.equal canon) |>
      Seq.fold ~init ~f:(fun acc x -> Map.set acc ~key:x ~data:(`var canon)))

module Make(M : Scalars.L) = struct
  open M

  module Analysis = Scalars.Make(M)

  let mkdef s x n = Map.update s x ~f:(function
      | None -> Range.singleton n
      | Some r -> Range.def r n)

  let mkuse s x n = Map.change s x ~f:(function
      | Some r -> Some (Range.use r n)
      | None -> None)

  let update acc s x n def = match Map.find s x with
    | Some Offset (base, _) ->
      if def then mkdef acc base n else mkuse acc base n
    | Some Top -> Map.set acc ~key:x ~data:Range.bad
    | None -> acc

  let liveness_insn acc s ip i =
    let op = Insn.op i in
    match Insn.load_or_store_to op with
    | Some (ptr, _, ldst) ->
      update acc s ptr ip @@ is_store ldst
    | None -> match Insn.offset op with
      | Some (ptr, _) ->
        update acc s ptr ip false
      | None -> match Insn.copy_of op with
        | Some x -> update acc s x ip false
        | None -> acc

  let liveness_ctrl acc s ip c =
    Ctrl.free_vars c |> Set.fold ~init:acc
      ~f:(fun acc x -> update acc s x ip false)

  let liveness cfg blks slots (s : solution) =
    let ip = ref 0 in
    let nums = Vec.create () in
    let acc =
      Graphlib.reverse_postorder_traverse
        (module Cfg) ~start:Label.pseudoentry cfg |>
      Seq.fold ~init:Var.Map.empty ~f:(fun acc l ->
          match Label.Tree.find blks l with
          | None -> acc
          | Some b ->
            let s = ref @@ Solution.get s l in
            let acc = Blk.insns b |> Seq.fold ~init:acc ~f:(fun acc i ->
                let op = Insn.op i in
                let acc = liveness_insn acc !s !ip i in
                Vec.push nums (Insn.label i);
                s := Analysis.transfer_op slots !s op;
                incr ip;
                acc) in
            let acc = liveness_ctrl acc !s !ip @@ Blk.ctrl b in
            Vec.push nums l;
            incr ip;
            acc) in
    acc, nums

  let run fn =
    let slots = Analysis.collect_slots fn in
    if Map.is_empty slots then Var.Map.empty else
      let cfg = Cfg.create fn in
      let blks = Func.map_of_blks fn in
      let s = Analysis.analyze ~cfg ~blks slots fn in
      let rs, nums = liveness cfg blks slots s in
      if debug then
        Map.iter_keys slots ~f:(fun x ->
            match Map.find rs x with
            | None ->
              Format.eprintf "%a: dead\n%!" Var.pp x
            | Some r when Range.is_bad r ->
              Format.eprintf "%a: top\n%!" Var.pp x
            | Some r ->
              Format.eprintf "%a: %a (%a to %a)\n%!" Var.pp x Range.pp r
                Label.pp (Vec.get_exn nums r.lo)
                Label.pp (Vec.get_exn nums r.hi)
          );
      let p = non_interfering slots rs in
      if debug then
        Partition.groups p |> Seq.iter ~f:(fun g ->
            Format.eprintf "%a\n%!" (Group.pp Var.pp) g
          );
      (* TODO: detect singleton ranges: these should be dead stores *)
      let subst = make_subst slots p in
      if debug then
        Map.iteri subst ~f:(fun ~key ~data ->
            Format.eprintf "%a => %a\n%!"
              Var.pp key Virtual.pp_operand data);
      subst
end
