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
let compat_range slots rs x y =
  compat_size_align slots x y &&
  let rx = Map.find_exn rs x in
  let ry = Map.find_exn rs y in
  let a : Allen.t = Range.Algebra.relate rx ry in
  Logs.debug (fun m ->
      m "%s: %a, %a: %a%!" __FUNCTION__ Var.pp x Var.pp y Allen.pp a);
  match a with
  | Before | After -> true
  | _ -> false

let range_priority rs x y =
  (* Prefer shorter live ranges. *)
  let rx = Map.find_exn rs x in
  let ry = Map.find_exn rs y in
  let c = Int.compare (Range.size rx) (Range.size ry) in
  if c = 0 then
    (* Break ties by comparing on the var. This
       is to give a bit more determinism to the
       algorithm. *)
    Var.compare x y
  else c

let size_priority slots x y =
  (* Assuming that the sizes and alignments are compatible,
     just pick the biggest one. *)
  let sx, ax = slot_sa slots x in
  let sy, ay = slot_sa slots y in
  match Int.compare sx sy with
  | 0 -> Int.compare ax ay
  | c -> c

let candidates rs =
  let vs = Vec.create ~capacity:(Map.length rs) () in
  Map.to_sequence rs |>
  (* Do not consider escapees. This would mess up
     our heuristics for building the groups. *)
  Seq.filter ~f:(not @. Range.is_bad @. snd) |>
  Seq.map ~f:fst |> Seq.iter ~f:(Vec.push vs);
  vs

let is_adjacent slots rs x y =
  Var.(x <> y) && compat_range slots rs x y

(* Greedy partitioning algorithm. *)
let partition slots rs =
  let vs = candidates rs in
  match Vec.length vs with
  | 0 -> []
  | 1 -> [Var.Set.singleton @@ Vec.front_exn vs]
  | len ->
    assert (len > 1);
    let gs = ref [] in
    let adj = Var.Table.create ~size:len () in
    let assigned = Var.Hash_set.create ~size:len () in
    (* Compute the adjacency table. *)
    Vec.iter vs ~f:(fun x ->
        Vec.to_sequence_mutable vs |>
        Seq.filter ~f:(is_adjacent slots rs x) |>
        Var.Set.of_sequence |> function
        | s when Set.is_empty s -> ()
        | s -> Hashtbl.set adj ~key:x ~data:s);
    (* Use an ascending order. *)
    Vec.sort vs ~compare:(fun x y -> range_priority rs y x);
    while not @@ Vec.is_empty vs do
      let x = Vec.pop_exn vs in
      Hash_set.strict_add assigned x |>
      Or_error.iter ~f:(fun () ->
          Logs.debug (fun m ->
              m "%s: processing %a%!"
                __FUNCTION__ Var.pp x);
          let g = Vec.fold_right vs
              ~init:(Var.Set.singleton x)
              ~f:(fun y g ->
                  (* Ensure that all groups are disjoint. *)
                  if Hash_set.mem assigned y then g
                  else match Hashtbl.find adj y with
                    | Some a when Set.is_subset g ~of_:a ->
                      (* Freeze `y` to this group. *)
                      Hash_set.add assigned y;
                      Set.add g y
                    | Some _ | None -> g) in
          gs := g :: !gs)
    done;
    !gs

(* invariant: a group is never empty *)
let canon_elt slots g =
  Set.to_sequence g |>
  Seq.max_elt ~compare:(size_priority slots) |>
  Option.value_exn

let make_subst slots p =
  List.fold p ~init:Var.Map.empty ~f:(fun init g ->
      if Set.length g <= 1 then init else
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

  let mkuse f s x n = Map.change s x ~f:(function
      | Some r -> Some (Range.use r n)
      | None -> f n)

  let update acc s x n ldst = match Map.find s x with
    | Some Top -> Map.set acc ~key:x ~data:Range.bad
    | Some Offset (base, _) ->
      begin match ldst with
        | None -> mkuse (const None) acc base n
        | Some Store -> mkdef acc base n
        | Some Load ->
          (* If we end up with a load from an uninitialized slot,
             then it is UB, and we shouldn't try to coalesce it
             with anything else. *)
          let f _ =
            Logs.debug (fun m ->
                m "%s: slot %a is loaded before being initialized"
                  __FUNCTION__ Var.pp base);
            Some Range.bad in
          mkuse f acc base n
      end
    | None -> acc

  let liveness_insn acc s ip i =
    let op = Insn.op i in
    let r = Insn.free_vars op in
    let r, w, ldst = match Insn.load_or_store_to op with
      | None -> r, None, None
      | Some (ptr, _, ldst) ->
        Set.remove r ptr, Some ptr, Some ldst in
    Option.fold w ~init:acc ~f:(fun acc x ->
        update acc s x ip ldst) |> fun init ->
    Set.fold r ~init ~f:(fun acc x ->
        update acc s x ip None)

  let liveness_ctrl acc s ip c =
    Ctrl.free_vars c |> Set.fold ~init:acc
      ~f:(fun acc x -> update acc s x ip None)

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
      let t = Analysis.analyze cfg blks slots in
      let rs, nums = liveness cfg blks slots t in
      let p = partition slots rs in
      let deads = collect_deads blks slots rs t in
      let subst = make_subst slots p in
      debug_show slots rs nums deads p subst;
      {subst; deads}
end
