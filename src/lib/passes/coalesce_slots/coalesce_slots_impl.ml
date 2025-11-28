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

type candidate = {
  var : Var.t;
  size : int;
  align : int;
  range : range;
  mutable adj : Var.Set.t;
  mutable assigned : bool;
}

let create_candidate slots rs v =
  let slot = Map.find_exn slots v in {
    var = v;
    size = Slot.size slot;
    align = Slot.align slot;
    range = Map.find_exn rs v;
    adj = Var.Set.empty;
    assigned = false;
  }

let compat_size_align x y =
  (* The smaller slot must not have a higher alignment. *)
  not ((x.size < y.size && x.align > y.align) ||
       (y.size < x.size && y.align > x.align))

(* Find compatible slots. Most importantly, their live ranges must
   not interfere. *)
let compat_range x y =
  compat_size_align x y &&
  let a : Allen.t = Range.Algebra.relate x.range y.range in
  Logs.debug (fun m ->
      m "%s: %a, %a: %a%!" __FUNCTION__
        Var.pp x.var Var.pp y.var Allen.pp a);
  match a with
  | Before | After -> true
  | _ -> false

let range_priority x y =
  (* Prefer shorter live ranges. *)
  let c = Int.compare (Range.size x.range) (Range.size y.range) in
  if c = 0 then
    (* Break ties by comparing on the var. This
       is to give a bit more determinism to the
       algorithm. *)
    Var.compare x.var y.var
  else c

let size_priority x y =
  (* Assuming that the sizes and alignments are compatible,
     just pick the biggest one. *)
  match Int.compare x.size y.size with
  | 0 -> Int.compare x.align y.align
  | c -> c

let candidates slots rs =
  let vs = Vec.create ~capacity:(Map.length rs) () in
  Map.to_sequence rs |>
  (* Do not consider escapees. This would mess up
     our heuristics for building the groups. *)
  Seq.filter ~f:(not @. Range.is_bad @. snd) |>
  Seq.map ~f:(create_candidate slots rs @. fst) |>
  Seq.iter ~f:(Vec.push vs);
  vs

let is_subset g y = List.for_all g ~f:(fun x -> Set.mem y.adj x.var)

(* Greedy partitioning algorithm. *)
let partition slots rs =
  let vs = candidates slots rs in
  match Vec.length vs with
  | 0 -> []
  | 1 -> [[Vec.front_exn vs]]
  | len ->
    assert (len > 1);
    let gs = ref [] in
    (* Compute the adjacency sets. *)
    for i = 0 to len - 1 do
      let x = Vec.unsafe_get vs i in
      for j = 0 to len - 1 do
        if i <> j then
          let y = Vec.unsafe_get vs j in
          if compat_range x y then
            x.adj <- Set.add x.adj y.var
      done
    done;
    (* Use an ascending order. *)
    Vec.sort vs ~compare:(fun x y -> range_priority y x);
    while not @@ Vec.is_empty vs do
      let x = Vec.pop_exn vs in
      if not x.assigned then
        let () = x.assigned <- true in
        Logs.debug (fun m ->
            m "%s: processing %a%!"
              __FUNCTION__ Var.pp x.var);
        let g = ref [x] in
        for i = Vec.length vs - 1 downto 0 do
          let y = Vec.unsafe_get vs i in
          if not y.assigned && is_subset !g y then
            let () = y.assigned <- true in
            g := y :: !g
        done;
        gs := !g :: !gs
    done;
    !gs

(* invariant: a group is never empty *)
let canon_elt g = List.max_elt g ~compare:size_priority |> Option.value_exn

let make_subst _slots p =
  List.fold p ~init:Var.Map.empty
    ~f:(fun init -> function
        | [] | [_] -> init
        | g ->
          let canon = canon_elt g in
          let data = `var canon.var in
          List.fold g ~init ~f:(fun acc x ->
              if Var.(x.var = canon.var) then acc
              else Map.set acc ~key:x.var ~data))

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

  module S = Slot_initialization.Make(M)

  let mkdef s x n = Map.update s x ~f:(function
      | None -> Range.singleton n
      | Some r -> Range.def r n)

  let mkuse s x n = Map.change s x ~f:(function
      | Some r -> Some (Range.use r n)
      | None -> None)

  let update (si : Slot_initialization.t) acc s x n l ldst =
    match Map.find s x with
    | None -> acc
    | Some Top -> Map.set acc ~key:x ~data:Range.bad
    | Some Offset (base, _) -> match ldst with
      | Some Store -> mkdef acc base n
      | Some Load when Hash_set.mem si.bad l ->
        (* Uninitialized load is UB: forbid this slot as
           a candidate for coalescing. *)
        Logs.debug (fun m ->
            m "%s: uninitialized load at %a from %a: marking bad%!"
              __FUNCTION__ Label.pp l Var.pp base);
        Map.set acc ~key:base ~data:Range.bad
      | Some Load | None -> mkuse acc base n

  let liveness_insn si acc s ip i =
    let l = Insn.label i and op = Insn.op i in
    let r = Insn.free_vars op in
    let r, w, ldst = match Insn.load_or_store_to op with
      | None -> r, None, None
      | Some (ptr, _, ldst) ->
        Set.remove r ptr, Some ptr, Some ldst in
    Option.fold w ~init:acc ~f:(fun acc x ->
        update si acc s x ip l ldst) |> fun init ->
    Set.fold r ~init ~f:(fun acc x ->
        update si acc s x ip l None)

  let liveness_ctrl si acc s ip l c =
    Ctrl.free_vars c |> Set.fold ~init:acc
      ~f:(fun acc x -> update si acc s x ip l None)

  let liveness cfg blks slots t si =
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
              let acc = liveness_insn si acc !s !ip i in
              Vec.push nums (Insn.label i);
              s := S.Analysis.transfer_op slots !s op;
              incr ip;
              acc) in
          let acc = liveness_ctrl si acc !s !ip l @@ Blk.ctrl b in
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
              s := S.Analysis.transfer_op slots !s op;
              acc))

  let debug_show slots rs nums deads p subst =
    Logs.debug (fun m ->
        Map.iter_keys slots ~f:(fun x ->
            let ppr ppf x = match Map.find rs x with
              | None -> Format.fprintf ppf "none"
              | Some r when Range.is_bad r ->
                Format.fprintf ppf "bad"
              | Some r ->
                Format.fprintf ppf "%a (%a to %a)"
                  Range.pp r
                  Label.pp (Vec.get_exn nums r.lo)
                  Label.pp (Vec.get_exn nums r.hi) in
            m "%s: %a: %a%!" __FUNCTION__ Var.pp x ppr x));
    Logs.debug (fun m ->
        List.iter p ~f:(fun g ->
            m "%s: group: %s%!" __FUNCTION__
              (List.to_string g ~f:(fun x ->
                   Var.to_string x.var))));
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
    let slots = S.Analysis.collect_slots fn in
    if Map.is_empty slots then empty else
      let cfg = Cfg.create fn in
      let blks = Func.map_of_blks fn in
      let t = S.Analysis.analyze cfg blks slots in
      let si = S.analyze' t cfg blks slots in
      let rs, nums = liveness cfg blks slots t si in
      let p = partition slots rs in
      let deads = collect_deads blks slots rs t in
      let subst = make_subst slots p in
      debug_show slots rs nums deads p subst;
      {subst; deads}
end
