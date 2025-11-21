open Core
open Regular.Std
open Graphlib.Std
open Scalars

module Ltree = Label.Tree
module Lset = Label.Tree_set
module Slot = Virtual.Slot
module Allen = Allen_interval_algebra

type tag = Def | Use | Both [@@deriving compare, equal, sexp]

let pp_tag ppf = function
  | Def -> Format.fprintf ppf "def"
  | Use -> Format.fprintf ppf "use"
  | Both -> Format.fprintf ppf "both"

let join_tag a b = if equal_tag a b then a else Both

type range = {
  lo : int;
  hi : int;
  tg : tag;
} [@@deriving compare, equal, sexp]

module Range = struct
  type t = range [@@deriving compare, equal, sexp]

  let pp ppf r = Format.fprintf ppf "%a[%d, %d]" pp_tag r.tg r.lo r.hi

  let bad = {lo = Int.min_value; hi = Int.max_value; tg = Both}
  let is_bad = equal bad

  let singleton n = {lo = n; hi = n; tg = Def}
  let size r = r.hi - r.lo

  let distance x y =
    if x.hi < y.lo then y.lo - x.hi
    else if x.lo > y.hi then x.lo - y.hi
    else 0
  [@@ocaml.warning "-32"]

  (* Extend the upper-bound on the live range. *)
  let use r n = {
    r with
    hi = Int.max r.hi n;
    tg = join_tag r.tg Use;
  }

  (* Shrink the lower-bound on the live range.

     Also, a defintion counts as a use, because we need to
     reference the slot, so extend the upper-bound.
  *)
  let def r n = {
    lo = Int.min r.lo n;
    hi = Int.max r.hi n;
    tg = join_tag r.tg Def;
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
  Logs.debug (fun m ->
      m "%s: %a, %a: %a%!" __FUNCTION__ Var.pp x Var.pp y Allen.pp a);
  match a with
  | Before | After -> true
  | _ -> false

let partition slots rs vs =
  let pick rem =
    Set.to_sequence rem |>
    Seq.min_elt ~compare:(fun x y ->
        (* Prefer shorter live ranges. *)
        let rx = Map.find_exn rs x in
        let ry = Map.find_exn rs y in
        let c = Int.compare (Range.size rx) (Range.size ry) in
        if c = 0 then
          (* Break ties by comparing on the var. This
             is to give a bit more determinism to the
             algorithm. *)
          Var.compare x y
        else c) in
  (* Ensure that `x` does not interfere with any of the
     slots in the group. *)
  let ok g x = Set.for_all g ~f:(equiv_range slots rs x) in
  let[@tail_mod_cons] rec go rem = match pick rem with
    | None -> []
    | Some seed ->
      let g = Set.fold rem ~init:(Var.Set.singleton seed)
          ~f:(fun g x -> if ok g x then Set.add g x else g) in
      g :: go (Set.diff rem g) in
  go vs

let non_interfering slots rs =
  Map.to_sequence rs |>
  (* Do not consider escapees. This would mess up
     our heuristics for building the groups. *)
  Seq.filter ~f:(not @. Range.is_bad @. snd) |>
  Seq.map ~f:fst |>
  Var.Set.of_sequence |>
  partition slots rs

(* invariant: a group is never empty *)
let canon_elt slots g =
  Set.to_sequence g |> Seq.max_elt ~compare:(fun x y ->
      (* Assuming that the sizes and alignments are compatible,
         just pick the biggest one. *)
      let sx, ax = slot_sa slots x in
      let sy, ay = slot_sa slots y in
      match Int.compare sx sy with
      | 0 -> Int.compare ax ay
      | c -> c) |>
  Option.value_exn

let make_subst slots p =
  List.fold p ~init:Var.Map.empty ~f:(fun init g ->
      let canon = canon_elt slots g in
      Set.to_sequence g |>
      Seq.filter ~f:(not @. Var.equal canon) |>
      Seq.fold ~init ~f:(fun acc x ->
          Map.set acc ~key:x ~data:(`var canon)))

type t = {
  subst : Subst_mapper.t; (* Map from coalesced to canonical slots *)
  deads : Lset.t;         (* Stores to dead slots. *)
}

let empty = {
  subst = Var.Map.empty;
  deads = Lset.empty;
}

let is_empty t =
  Map.is_empty t.subst && Lset.is_empty t.deads

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
    let r = Insn.free_vars op in
    let r, w = match Insn.load_or_store_to op with
      | Some (ptr, _, Store) -> Set.remove r ptr, Some ptr
      | Some _ | None -> r, None in
    Option.fold w ~init:acc ~f:(fun acc x ->
        update acc s x ip true) |> fun init ->
    Set.fold r ~init ~f:(fun acc x ->
        update acc s x ip false)

  let liveness_ctrl acc s ip c =
    Ctrl.free_vars c |> Set.fold ~init:acc
      ~f:(fun acc x -> update acc s x ip false)

  let liveness cfg blks slots t =
    let ip = ref 0 in
    let nums = Vec.create () in
    let init =
      Hash_set.fold t.esc ~init:Var.Map.empty
        ~f:(fun acc x -> Map.set acc ~key:x ~data:Range.bad) in
    let acc =
      Graphlib.reverse_postorder_traverse
        (module Cfg) ~start:Label.pseudoentry cfg |>
      Seq.filter_map ~f:(Ltree.find blks) |>
      Seq.fold ~init ~f:(fun acc b ->
          let l = Blk.label b in
          let s = ref @@ get t l in
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

  let collect_deads blks slots rs t =
    Ltree.fold blks ~init:Lset.empty
      ~f:(fun ~key ~data:b init ->
          let s = ref @@ get t key in
          Blk.insns b |> Seq.fold ~init ~f:(fun acc i ->
              let op = Insn.op i in
              let acc = match Insn.load_or_store_to op with
                | Some (ptr, _, Store) ->
                  begin match Map.find !s ptr with
                    | Some Offset (base, _) ->
                      begin match Map.find rs base with
                        | Some {tg = Def; _} ->
                          (* This slot is only ever stored to, so we can
                             safely remove it. *)
                          Lset.add acc @@ Insn.label i
                        | _ -> acc
                      end
                    | _ -> acc
                  end
                | _ -> acc in
              s := Analysis.transfer_op slots !s op;
              acc))

  let debug_show slots rs nums deads p subst =
    Logs.debug (fun m ->
        Map.iter_keys slots ~f:(fun x ->
            let ppr ppf x = match Map.find rs x with
              | None -> Format.fprintf ppf "none"
              | Some r when Range.is_bad r ->
                Format.fprintf ppf "escapes"
              | Some r ->
                Format.fprintf ppf "%a (%a to %a)"
                  Range.pp r
                  Label.pp (Vec.get_exn nums r.lo)
                  Label.pp (Vec.get_exn nums r.hi) in
            m "%s: %a: %a%!" __FUNCTION__ Var.pp x ppr x));
    Logs.debug (fun m ->
        List.iter p ~f:(fun g ->
            m "%s: group: %s%!" __FUNCTION__
              (Set.to_list g |> List.to_string ~f:Var.to_string)));
    Logs.debug (fun m ->
        if not @@ Lset.is_empty deads then
          m "%s: dead stores: %a%!"
            __FUNCTION__
            (Format.pp_print_list
               ~pp_sep:(fun ppf () -> Format.fprintf ppf ", ")
               Label.pp)
            (Lset.to_list deads));
    Logs.debug (fun m ->
        Map.iteri subst ~f:(fun ~key ~data ->
            m "%s: coalesce slot: %a => %a%!"
              __FUNCTION__ Var.pp key Virtual.pp_operand data))

  let run fn =
    let slots = Analysis.collect_slots fn in
    if Map.is_empty slots then empty else
      let cfg = Cfg.create fn in
      let blks = Func.map_of_blks fn in
      let t = Analysis.analyze ~cfg ~blks slots fn in
      let rs, nums = liveness cfg blks slots t in
      let p = non_interfering slots rs in
      let deads = collect_deads blks slots rs t in
      let subst = make_subst slots p in
      debug_show slots rs nums deads p subst;
      {subst; deads}
end
