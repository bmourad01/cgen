open Core
open Regular.Std
open Graphlib.Std
open Scalars
open Cgen_containers

module Ltree = Label.Tree
module Lset = Label.Tree_set
module LS = Label.Dense_set
module LT = Label.Dense_table
module Vtree = Var.Tree
module Vset = Var.Tree_set
module VS = Var.Dense_set
module Slot = Virtual.Slot
module Allen = Cgen_utils.Allen_interval_algebra

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

  let singleton n = {lo = n; hi = n + 1; tg = Def}
  let size r = r.hi - r.lo

  let distance x y =
    if x.hi < y.lo then y.lo - x.hi
    else if x.lo > y.hi then x.lo - y.hi
    else 0
  [@@ocaml.warning "-32"]

  (* Extend the upper-bound on the live range. *)
  let use r n = {
    r with
    hi = Int.max r.hi (n + 1);
    tg = join_tag r.tg Use;
  }

  (* Shrink the lower-bound on the live range.

     Also, a defintion counts as a use, because we need to
     reference the slot, so extend the upper-bound.
  *)
  let def r n = {
    lo = Int.min r.lo n;
    hi = Int.max r.hi (n + 1);
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
  mutable assigned : bool;
}

let create_candidate slots rs v =
  let slot = Vtree.find_exn slots v in {
    var = v;
    size = Slot.size slot;
    align = Slot.align slot;
    range = Vtree.find_exn rs v;
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
  | Before | After | Meets | Met_by -> true
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
  let vs = Vec.create ~capacity:(Vtree.length rs) () in
  Vtree.to_sequence rs |>
  (* Do not consider escapees. This would mess up
     our heuristics for building the groups. *)
  Seq.filter ~f:(not @. Range.is_bad @. snd) |>
  Seq.map ~f:(create_candidate slots rs @. fst) |>
  Seq.iter ~f:(Vec.push vs);
  vs

(* Greedy partitioning algorithm. *)
let partition slots rs =
  let vs = candidates slots rs in
  match Vec.length vs with
  | 0 -> []
  | 1 -> [[Vec.front_exn vs]]
  | len ->
    assert (len > 1);
    (* Process shorter live ranges first. *)
    Vec.sort vs ~compare:(fun x y -> range_priority y x);
    let gs = ref [] in
    let feasible = ref (Bitset.create ~capacity:len ()) in
    let scratch = ref (Bitset.create ~capacity:len ()) in
    for k = len - 1 downto 0 do
      let x = Vec.unsafe_get vs k in
      if not x.assigned then begin
        x.assigned <- true;
        Logs.debug (fun m ->
            m "%s: processing %a%!"
              __FUNCTION__ Var.pp x.var);
        let g = ref [x] in
        (* Seed every unassigned candidate below `k` that is
           compatible with `x`. *)
        Bitset.clear !feasible;
        for j = 0 to k - 1 do
          let y = Vec.unsafe_get vs j in
          if not y.assigned && compat_range x y then
            Bitset.add !feasible j
        done;
        for i = k - 1 downto 0 do
          if Bitset.mem !feasible i then begin
            let y = Vec.unsafe_get vs i in
            y.assigned <- true;
            g := y :: !g;
            (* feasible := feasible ∩ {j | compat y vs[j]}. *)
            Bitset.clear !scratch;
            Bitset.iter !feasible ~f:(fun j ->
                if compat_range y (Vec.unsafe_get vs j)
                then Bitset.add !scratch j);
            Ref.swap feasible scratch
          end
        done;
        gs := !g :: !gs
      end
    done;
    !gs

(* invariant: a group is never empty *)
let canon_elt g = List.max_elt g ~compare:size_priority |> Option.value_exn

let make_subst _slots p =
  List.fold p ~init:Vtree.empty
    ~f:(fun init -> function
        | [] | [_] -> init
        | g ->
          let canon = canon_elt g in
          let data = `var canon.var in
          List.fold g ~init ~f:(fun acc x ->
              if Var.(x.var = canon.var) then acc
              else Vtree.set acc ~key:x.var ~data))

type t = {
  subst : Subst_mapper.t; (* Map from coalesced to canonical slots *)
  deads : Lset.t;         (* Stores to dead slots. *)
}

let empty = {
  subst = Vtree.empty;
  deads = Lset.empty;
}

let is_empty t =
  Vtree.is_empty t.subst && Lset.is_empty t.deads

module Make(M : Scalars.L) = struct
  open M

  module Sinit = Slot_initialization.Make(M)
  module Loop = Loops.Make(M.Cfg)

  let mkdef s x n = Vtree.update_with s x
      ~nil:(fun () -> Range.singleton n)
      ~has:(fun r -> Range.def r n)

  let mkuse s x n = Vtree.change s x ~f:(function
      | Some r -> Some (Range.use r n)
      | None -> None)

  let update (si : Slot_initialization.t) acc s x n l ldst =
    match Vtree.find s x with
    | None -> acc
    | Some Top -> Vtree.set acc ~key:x ~data:Range.bad
    | Some Offset (base, _) -> match ldst with
      | Some Store -> mkdef acc base n
      | Some Load when LS.mem si.bad l ->
        (* Uninitialized load is UB: forbid this slot as
           a candidate for coalescing. *)
        Logs.debug (fun m ->
            m "%s: uninitialized load at %a from %a: marking bad%!"
              __FUNCTION__ Label.pp l Var.pp base);
        Vtree.set acc ~key:base ~data:Range.bad
      | Some Load | None -> mkuse acc base n

  let liveness_insn si acc s ip i =
    let l = Insn.label i and op = Insn.op i in
    let r = Insn.free_vars op in
    let r, w, ldst = match Insn.load_or_store_to op with
      | None -> r, None, None
      | Some (ptr, _, ldst) ->
        Vset.remove r ptr, Some ptr, Some ldst in
    Option.fold w ~init:acc ~f:(fun acc x ->
        update si acc s x ip l ldst) |> fun init ->
    Vset.fold r ~init ~f:(fun acc x ->
        update si acc s x ip l None)

  let liveness_ctrl si acc s ip l c =
    Ctrl.free_vars c |> Vset.fold ~init:acc
      ~f:(fun acc x -> update si acc s x ip l None)

  (* Stretch slot ranges around loop back-edges *)
  let extend_for_loops loop spans rs =
    let loop_spans =
      Ltree.fold spans ~init:Ltree.empty
        ~f:(fun ~key:l ~data:(lo, hi) acc ->
            Loop.loops_of loop l |>
            Seq.fold ~init:acc ~f:(fun acc lp ->
                let h = Loop.header @@ Loop.get loop lp in
                Ltree.update_with acc h
                  ~has:(fun (a, b) -> Int.min a lo, Int.max b hi)
                  ~nil:(fun () -> lo, hi))) in
    if Ltree.is_empty loop_spans then rs else
      Vtree.fold rs ~init:rs ~f:(fun ~key ~data:r acc ->
          if Range.is_bad r then acc else
            let r' =
              Ltree.fold loop_spans ~init:r
                ~f:(fun ~key:_ ~data:(llo, lhi) r ->
                    (* Defined before the loop and reaching into it. *)
                    if r.lo < llo && r.hi > llo
                    then {r with hi = Int.max r.hi (lhi + 1)}
                    else r) in
            if phys_equal r' r then acc
            else Vtree.set acc ~key ~data:r')

  let compute_postord cfg blks =
    let open struct
      type frame =
        | Exit of Label.t
        | Enter of Label.t
    end in
    let n = Cfg.number_of_nodes cfg in
    let postord = Vec.create ~capacity:n () in
    let vis = LS.create ~capacity:n () in
    let q = Stack.singleton @@ Enter Label.pseudoentry in
    Stack.until_empty q (function
        | Exit u ->
          Ltree.find blks u |> Option.iter ~f:(Vec.push postord)
        | Enter u ->
          if LS.strict_add vis u then begin
            Stack.push q @@ Exit u;
            Cfg.Node.succs u cfg |>
            Seq.filter ~f:(Fn.non @@ LS.mem vis) |>
            Seq.to_list_rev |>
            List.iter ~f:(fun v ->
                Stack.push q @@ Enter v)
          end);
    postord

  let liveness cfg blks slots t si =
    let loop = Loop.analyze ~name:"" cfg in
    let ip = ref 0 in
    let nums = Vec.create () in
    let spans = ref Ltree.empty in
    let store_base = LT.create () in
    let init =
      VS.fold t.esc ~init:Vtree.empty
        ~f:(fun acc x -> Vtree.set acc ~key:x ~data:Range.bad) in
    let po = compute_postord cfg blks in
    let acc = Vec.fold_right po ~init ~f:(fun b acc ->
        let l = Blk.label b in
        let lo_ip = !ip in
        let s = ref @@ get t l in
        let acc = Blk.insns b |> Seq.fold ~init:acc ~f:(fun acc i ->
            let op = Insn.op i in
            let acc = liveness_insn si acc !s !ip i in
            let () = match Insn.load_or_store_to op with
              | Some (ptr, _, Store) ->
                begin match Vtree.find !s ptr with
                  | Some Offset (base, _) ->
                    LT.set store_base ~key:(Insn.label i) ~data:base
                  | _ -> ()
                end
              | _ -> () in
            Vec.push nums (Insn.label i);
            s := Sinit.S.transfer_op slots !s op;
            incr ip;
            acc) in
        let ctrl_ip = !ip in
        let acc = liveness_ctrl si acc !s ctrl_ip l @@ Blk.ctrl b in
        Vec.push nums l;
        incr ip;
        spans := Ltree.set !spans ~key:l ~data:(lo_ip, ctrl_ip);
        acc) in
    extend_for_loops loop !spans acc, nums, store_base

  let collect_deads rs store_base =
    LT.fold store_base ~init:Lset.empty
      ~f:(fun ~key:label ~data:base acc ->
          match Vtree.find rs base with
          | Some {tg = Def; _} ->
            (* This slot is only ever stored to, so we can safely
               remove it. *)
            Lset.add acc label
          | _ -> acc)

  let debug_show slots rs nums deads p subst =
    Logs.debug (fun m ->
        Vtree.iter slots ~f:(fun ~key:x ~data:_ ->
            let ppr ppf x = match Vtree.find rs x with
              | None -> Format.fprintf ppf "none"
              | Some r when Range.is_bad r ->
                Format.fprintf ppf "bad"
              | Some r ->
                Format.fprintf ppf "%a (%a to %a)"
                  Range.pp r
                  Label.pp (Vec.get_exn nums r.lo)
                  Label.pp (Vec.get_exn nums (r.hi - 1)) in
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
        Vtree.iter subst ~f:(fun ~key ~data ->
            m "%s: coalesce slot: %a => %a%!"
              __FUNCTION__ Var.pp key Virtual.pp_operand data))

  let run fn =
    let slots = Sinit.S.collect_slots fn in
    if Vtree.is_empty slots then empty else
      let cfg = Cfg.create fn in
      let blks = Func.map_of_blks fn in
      let t = Sinit.S.analyze cfg blks slots in
      let si = Sinit.analyze' t cfg blks slots in
      let rs, nums, store_base = liveness cfg blks slots t si in
      let p = partition slots rs in
      let deads = collect_deads rs store_base in
      let subst = make_subst slots p in
      debug_show slots rs nums deads p subst;
      {subst; deads}
end
