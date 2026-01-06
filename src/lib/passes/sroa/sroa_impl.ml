(* A conservative implementation of SROA (Scalar Replacement of Aggregates).

   Most notably, we don't consider compound/aggregate types at all. Why?
   Because they are second-class citizens in our IR, and they are highly
   dependent on the implementation details of the target ABI.

   After ABI lowering, they are desugared, after which this pass becomes
   more useful.
*)

open Core
open Regular.Std
open Scalars

module Slot = Virtual.Slot
module Allen = Allen_interval_algebra

type range = {
  lo : int64;
  hi : int64;
}

module Range = struct
  type t = range
  let lo r = r.lo [@@inline]
  let hi r = r.hi [@@inline]
  let size r = Int64.(r.hi - r.lo) [@@inline]
  let coverage a b = Int64.(b.hi - a.lo) [@@inline]
  let pp ppf r = Format.fprintf ppf "[0x%Lx, 0x%Lx)" r.lo r.hi
end

module Algebra = Allen.Make(struct
    include Range
    type point = int64
    include Int64.Replace_polymorphic_compare
  end)

let basic_size ty = Type.sizeof_basic ty / 8 [@@inline]

(* A partition of elements at a particular offset+size range. *)
type 'a partition = {
  off  : int64;
  size : int64;
  mems : 'a list;
}

type 'a partitions = 'a partition list Var.Map.t

module Partition = struct
  type 'a t = 'a partition

  let cmp a b = Int64.compare a.off b.off

  (* Check if a partition covers the entire slot `s`. *)
  let is_entire_slot s p = match p.off with
    | 0L -> Int64.(of_int (Slot.size s) = p.size)
    | _ -> false
  [@@inline]

  let range p = {
    lo = p.off;
    hi = Int64.(p.off + max 1L p.size);
  } [@@inline]

  let pp ppa ppf p =
    Format.fprintf ppf "0x%Lx:%Ld: %a"
      p.off p.size
      (Format.pp_print_list
         ~pp_sep:(fun ppf () -> Format.fprintf ppf " ")
         ppa) p.mems

  let add_member x p = {p with mems = x :: p.mems} [@@inline]
  let change off size x p = {off; size; mems = x :: p.mems} [@@inline]
  let singleton off size x = {off; size; mems = [x]} [@@inline]
end

module Make(M : Scalars.L) : sig
  val run : M.Func.t -> M.Func.t Context.t
end = struct
  open M

  module Analysis = Scalars.Make(M)

  (* A memory access for a slot. *)
  type access = {
    insn : Insn.t;
    off  : int64;
    ty   : Type.basic;
    ldst : load_or_store;
  }

  type accesses = access list Var.Map.t

  module Access = struct
    type t = access [@@ocaml.warning "-34"]

    let sizeof a = basic_size a.ty [@@inline]

    let cmp a b =
      match Int64.compare a.off b.off with
      | 0 -> Int.compare (sizeof a) (sizeof b)
      | c -> c

    let range a = {
      lo = a.off;
      hi = Int64.(a.off + max 1L (of_int (sizeof a)));
    } [@@inline]

    let pp ppf a =
      let neg = Int64.is_negative a.off in
      let pre, off = if neg then '-', Int64.neg a.off else '+', a.off in
      Format.fprintf ppf "%a[%a.%a,%c0x%Lx]"
        Label.pp (Insn.label a.insn)
        pp_load_or_store a.ldst
        Type.pp_basic a.ty
        pre off
  end

  let collect_accesses slots fn t : accesses =
    (* Group all memory accesses by their corresponding slot. *)
    Func.blks fn |> Seq.fold ~init:Var.Map.empty ~f:(fun init b ->
        let s = ref @@ get t @@ Blk.label b in
        Blk.insns b |> Seq.fold ~init ~f:(fun acc insn ->
            let op = Insn.op insn in
            let acc = match Insn.load_or_store_to op with
              | None -> acc
              | Some (ptr, ty, ldst) -> match Map.find !s ptr with
                | Some Offset (base, _) when escaped t base ->
                  (* Any slot that escaped at any time should not
                     be considered for partitioning. *)
                  Logs.debug (fun m ->
                      m "%s: ignoring escaped pointer %a%!"
                        __FUNCTION__ Var.pp base);
                  acc
                | Some Offset (base, off) ->
                  Map.add_multi acc ~key:base ~data:{insn; off; ty; ldst}
                | _ -> acc in
            s := Analysis.transfer_op slots !s op;
            acc)) |>
    Map.map ~f:(List.sort ~compare:Access.cmp)

  (* Sort the memory accesses into self-contained, non-overlapping
     partitions, which are the fully-or-partially scalarized sub-objects
     of the aggregate. *)
  let partition_acesses : accesses -> access partitions = fun m ->
    let rec merge acc c = function
      | [] -> List.sort (c :: acc) ~compare:Partition.cmp
      | x :: xs ->
        let rc = Partition.range c in
        let rx = Access.range x in
        let a = Algebra.relate rc rx in
        let acc, p = match a with
          | Equal | Started_by | Finished_by | Contains ->
            (* Partition subsumes the access. *)
            acc, Partition.add_member x c
          | During | Finishes ->
            (* Access subsumes the partition *)
            acc, Partition.change rx.lo (Range.size rx) x c
          | Overlaps | Starts ->
            (* Extend the upper bound. *)
            acc, Partition.change rc.lo (Range.coverage rc rx) x c
          | Overlapped_by ->
            (* Extend the lower bound. *)
            acc, Partition.change rx.lo (Range.coverage rx rc) x c
          | Before | After | Meets | Met_by ->
            (* No overlap, so we start a new partition. *)
            let sx = Int64.of_int @@ Access.sizeof x in
            c :: acc, Partition.singleton x.off sx x in
        Logs.debug (fun m ->
            m "%s: partition %a, access %a: %a%!"
              __FUNCTION__ Range.pp rc Range.pp rx Allen.pp a);
        merge acc p xs in
    (* pre: each access list is sorted *)
    Map.filter_map m ~f:(function
        | [] -> None
        | x :: xs ->
          let sx = Int64.of_int @@ Access.sizeof x in
          let p = Partition.singleton x.off sx x in
          Some (merge [] p xs))

  (* Turn each partition into a concrete slot. *)
  let materialize_partitions slots parts : scalars Context.t =
    Map.to_sequence parts |> Seq.filter_map ~f:(fun (base, ps) ->
        Map.find slots base |> Option.map ~f:(fun s -> base, ps, s)) |>
    Context.Seq.fold ~init:Scalar.Map.empty ~f:(fun init (base, ps, s) ->
        Seq.of_list ps |> Seq.filter ~f:(not @. Partition.is_entire_slot s) |>
        Context.Seq.fold ~init ~f:(fun acc p ->
            let open Context.Syntax in
            let size = Int64.to_int_exn p.size in
            (* TODO: look through `p.mems` and see if there is a store
               that is larger than other acesses (i.e. `st.l` followed
               by one or more `ld.w`). If so, this partition could be
               broken down further if we modify the store instruction(s). *)
            let* x = Context.Var.fresh in
            let+? s = Slot.create x ~size ~align:size in
            Logs.debug (fun m ->
                m "%s: new slot %a, base=%a, off=0x%Lx, size=%Ld%!"
                  __FUNCTION__ Var.pp x Var.pp base p.off p.size);
            Map.set acc ~key:(base, p.off) ~data:s))

  (* Find the corresponding partition for [base+off, base+off+size). *)
  let find_partition (parts : 'a partitions) base off size =
    Map.find parts base |> Option.bind ~f:(fun ps ->
        let r = {lo = off; hi = Int64.(off + of_int size)} in
        List.find ps ~f:(fun (p : 'a partition) ->
            let rp = Partition.range p in
            let a = Algebra.relate r rp in
            Logs.debug (fun m ->
                m "%s: relating %a to %a: %a%!"
                  __FUNCTION__ Range.pp r Range.pp rp Allen.pp a);
            match a with
            | Starts | During | Finishes | Equal -> true
            | _ -> false))

  (* Exact cover for a scalar at `base + off`. *)
  let rewrite_insn_exact (m : scalars) i ~exact ~base ~off =
    let open Context.Syntax in
    Logs.debug (fun m ->
        m "%s: exact=0x%Lx, off=0x%Lx, base=%a%!"
          __FUNCTION__ exact off Var.pp base);
    let op = Insn.op i in
    let delta = Int64.(off - exact) in
    match Map.find m (base, exact) with
    | None ->
      Logs.debug (fun m -> m "%s: no slot found%!" __FUNCTION__);
      !![i]
    | Some s when Int64.(delta = 0L) ->
      Logs.debug (fun m ->
          m "%s: found slot %a (base)%!"
            __FUNCTION__ Var.pp (Slot.var s));
      (* Store to base of new slot. *)
      let addr = Slot.var s in
      let op' = Insn.replace_load_or_store_addr addr op in
      !![Insn.with_op i op']
    | Some s ->
      Logs.debug (fun m ->
          m "%s: found slot %a (delta 0x%Lx)%!"
            __FUNCTION__ Var.pp (Slot.var s) delta);
      (* Compute offset of new slot and store to it. *)
      let* l = Context.Label.fresh in
      let* y = Context.Var.fresh in
      let+ word = Context.target >>| Target.word in
      let a = Insn.add y word (Slot.var s) delta in
      let op' = Insn.replace_load_or_store_addr y op in
      [Insn.create ~label:l a; Insn.with_op i op']

  let debug_show_insn i ptr ty ldst =
    Logs.debug (fun m ->
        m "%s: %a: looking at %a.%a to %a%!"
          __FUNCTION__
          Label.pp (Insn.label i)
          pp_load_or_store ldst
          Type.pp_basic ty
          Var.pp ptr)

  let debug_show_bad_val ptr v =
    Logs.debug (fun m ->
        m "%s: cannot rewrite: %a is %a"
          __FUNCTION__ Var.pp ptr
          (Format.pp_print_option
             ~none:pp_bot
             pp_value)
          v)

  (* Rewrite an instruction. *)
  let rewrite_insn parts (m : scalars) (s : state) i =
    let open Context.Syntax in
    let op = Insn.op i in
    match Insn.load_or_store_to op with
    | None -> !![i]
    | Some (ptr, ty, ldst) ->
      debug_show_insn i ptr ty ldst;
      match Map.find s ptr with
      | (Some Top | None) as v ->
        debug_show_bad_val ptr v;
        !![i]
      | Some Offset (base, off) ->
        match find_partition parts base off @@ basic_size ty with
        | Some p -> rewrite_insn_exact m i ~exact:p.off ~base ~off
        | None ->
          Logs.debug (fun m -> m "%s: no parts found%!" __FUNCTION__);
          !![i]

  let rewrite_with_partitions slots fn t parts m =
    let open Context.Syntax in
    let* blks = Func.blks fn |> Context.Seq.map ~f:(fun b ->
        let s = ref @@ get t @@ Blk.label b in
        let+ insns = Blk.insns b |> Context.Seq.map ~f:(fun i ->
            let+ is = rewrite_insn parts m !s i in
            s := Analysis.transfer_op slots !s @@ Insn.op i; is)
          >>| List.concat @. Seq.to_list in
        Blk.with_insns b insns) >>| Seq.to_list in
    Context.lift_err @@ Func.with_blks fn blks

  let insert_new_slots fn m = Map.fold m ~init:fn
      ~f:(fun ~key:_ ~data fn -> Func.insert_slot fn data)

  let debug_show_parts parts =
    Logs.debug (fun m ->
        m "%s: partitions:\n%a%!"
          __FUNCTION__
          (Format.pp_print_list
             ~pp_sep:(fun ppf () -> Format.fprintf ppf "\n")
             (fun ppf (key, data) ->
                Format.fprintf ppf "%a:\n%a"
                  Var.pp key
                  (Format.pp_print_list
                     ~pp_sep:(fun ppf () -> Format.fprintf ppf "\n")
                     (fun ppf -> Format.fprintf ppf "  %a"
                         (Partition.pp Access.pp)))
                  data))
          (Map.to_alist parts))

  (* XXX: allowing the analysis to propagate through block parameters
     could possibly be done, but the current transformation isn't
     set up to properly handle it.

     The main issue arises from pointers into the slots that get
     aliased via a block parameter. That dangling reference will
     currently be left unchanged, leading to garbage values being
     read from the old slot.
  *)
  let analyze slots fn =
    Analysis.analyze ~blkparam:false slots fn

  let run fn =
    let open Context.Syntax in
    let slots = Analysis.collect_slots fn in
    if Map.is_empty slots then !!fn else
      let cfg = Cfg.create fn in
      let blks = Func.map_of_blks fn in
      let t = analyze cfg blks slots in
      let accs = collect_accesses slots fn t in
      let parts = partition_acesses accs in
      if Map.is_empty parts then !!fn else
        let () = debug_show_parts parts in
        let* m = materialize_partitions slots parts in
        if Map.is_empty m then !!fn else
          let fn = insert_new_slots fn m in
          rewrite_with_partitions slots fn t parts m
end
