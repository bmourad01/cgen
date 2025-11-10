(* A conservative implementation of SROA (Scalar Replacement of Aggregates).

   Most notably, we don't consider compound/aggregate types at all. Why?
   Because they are second-class citizens in our IR, and they are highly
   dependent on the implementation details of the target ABI.

   After ABI lowering, they are desugared, after which this pass becomes
   more useful.
*)

open Core
open Regular.Std
open Graphlib.Std
open Scalars

let debug = false

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

  let basic_size ty = Type.sizeof_basic ty / 8
  let sizeof_access a = basic_size a.ty

  let cmp_access a b =
    match Int64.compare a.off b.off with
    | 0 -> Int.compare (sizeof_access a) (sizeof_access b)
    | c -> c

  let pp_access ppf a =
    let neg = Int64.is_negative a.off in
    let pre, off = if neg then '-', Int64.neg a.off else '+', a.off in
    Format.fprintf ppf "(%a %a.%a %c0x%Lx)"
      Label.pp (Insn.label a.insn)
      pp_load_or_store a.ldst
      Type.pp_basic a.ty
      pre off

  let collect_accesses slots fn (s : solution) : accesses =
    (* Group all memory accesses by their corresponding slot. *)
    Func.blks fn |> Seq.fold ~init:Var.Map.empty ~f:(fun init b ->
        let s = ref @@ Solution.get s @@ Blk.label b in
        Blk.insns b |> Seq.fold ~init ~f:(fun acc i ->
            let op = Insn.op i in
            let acc = match Insn.load_or_store_to op with
              | None -> acc
              | Some (ptr, ty, ldst) -> match Map.find !s ptr with
                | Some Offset (base, off) ->
                  Map.add_multi acc ~key:base ~data:{insn = i; off; ty; ldst}
                | _ -> acc in
            s := Analysis.transfer_op slots !s op;
            acc)) |>
    (* Filter out slots that are not splittable. *)
    Map.map ~f:(List.sort ~compare:cmp_access) |>
    Map.filteri ~f:(fun ~key ~data ->
        let check x y=
          let sx = sizeof_access x in
          (* No partial overlaps. *)
          Int64.(x.off + of_int sx <= y.off) ||
          (* Allow exact re-use of the same region. *)
          cmp_access x y = 0 in
        let rec ok = function
          | x :: ((y :: _) as xs) -> check x y && ok xs
          | [] | [_] -> true in
        let res = ok data in
        if debug && not res then
          Format.eprintf "filtering out accesses for %a\n%!" Var.pp key;
        res)

  let overlaps oa sa ob sb =
    Int64.(oa < ob + of_int sb && ob < oa + of_int sa)

  let within oa sa ob sb =
    Int64.(oa >= ob && oa + of_int sa <= ob + of_int sb)

  (* A partition of memory accesses at a particular offset+size range. *)
  type partition = {
    off  : int64;
    size : int;
    mems : access list;
  }

  type partitions = partition list Var.Map.t

  let cmp_partition a b = Int64.compare a.off b.off

  (* Check if a partition covers the entire slot `s`. *)
  let is_entire_slot s p = match p.off with
    | 0L -> Virtual.Slot.size s = p.size
    | _ -> false

  let pp_partition ppf p =
    Format.fprintf ppf "0x%Lx:%d: @[%a@]"
      p.off p.size
      (Format.pp_print_list
         ~pp_sep:(fun ppf () -> Format.fprintf ppf " ")
         pp_access) p.mems

  (* Sort the memory accesses into self-contained, non-overlapping
     partitions, which are the fully-or-partially scalarized sub-objects
     of the aggregate. *)
  let partition_acesses m : partitions =
    let rec merge acc c = function
      | [] -> List.sort (c :: acc) ~compare:cmp_partition
      | x :: xs ->
        let sx = sizeof_access x in
        if Int64.(c.off = x.off) && c.size = sx then
          (* Access exactly matches the current partition. *)
          merge acc {c with mems = x :: c.mems} xs
        else if overlaps c.off c.size x.off sx then
          (* Access overlaps with current partition, so the partition
             must increase in size. *)
          let o' = Int64.min c.off x.off in
          let e' = Int64.(max (c.off + of_int c.size) (x.off + of_int sx)) in
          let s' = Int64.(to_int_exn (e' - o')) in
          merge acc {
            off = o';
            size = s';
            mems = x :: c.mems;
          } xs
        else
          (* No overlap, so we start a new partition. *)
          merge (c :: acc) {
            off = x.off;
            size = sx;
            mems = [x];
          } xs in
    (* pre: each access list is sorted *)
    Map.map m ~f:(function
        | [] -> []
        | (x : access) :: xs ->
          merge [] {
            off = x.off;
            size = sizeof_access x;
            mems = [x];
          } xs)

  (* Turn each partition into a concrete slot. *)
  let materialize_partitions slots parts : scalars Context.t =
    Map.to_sequence parts |> Seq.filter_map ~f:(fun (base, ps) ->
        Map.find slots base |> Option.map ~f:(fun s -> base, ps, s)) |>
    Context.Seq.fold ~init:Scalar.Map.empty ~f:(fun init (base, ps, s) ->
        Seq.of_list ps |> Seq.filter ~f:(not @. is_entire_slot s) |>
        Context.Seq.fold ~init ~f:(fun acc p ->
            let open Context.Syntax in
            (* TODO: look through `p.mems` and see if there is a store
               that is larger than other acesses (i.e. `st.l` followed
               by one or more `ld.w`). If so, this partition could be
               broken down further if we modify the store instruction(s). *)
            let* x = Context.Var.fresh in
            let*? s = Virtual.Slot.create x ~size:p.size ~align:p.size in
            if debug then
              Format.eprintf "new slot %a, base=%a, off=0x%Lx, size=%d\n%!"
                Var.pp x Var.pp base p.off p.size;
            !!(Map.set acc ~key:(base, p.off) ~data:s)))

  (* Find the corresponding partition for [base+off, base+off+size). *)
  let find_partition (parts : partitions) base off size =
    Map.find parts base |>
    Option.bind ~f:(List.find ~f:(fun p ->
        within off size p.off p.size))

  (* Exact cover for a scalar at `base + off`. *)
  let rewrite_insn_exact (m : scalars) i ~exact ~base ~off =
    let open Context.Syntax in
    if debug then
      Format.eprintf "exact=0x%Lx, off=0x%Lx, base=%a\n%!"
        exact off Var.pp base;
    let op = Insn.op i in
    let delta = Int64.(off - exact) in
    match Map.find m (base, exact) with
    | None ->
      if debug then
        Format.eprintf "no slot found\n%!";
      !![i]
    | Some s when Int64.(delta = 0L) ->
      if debug then
        Format.eprintf "found slot %a (base)\n%!"
          Var.pp (Virtual.Slot.var s);
      (* Store to base of new slot. *)
      let addr = Virtual.Slot.var s in
      let op' = Insn.replace_load_or_store_addr addr op in
      !![Insn.with_op i op']
    | Some s ->
      if debug then
        Format.eprintf "found slot %a (delta 0x%Lx)\n%!"
          Var.pp (Virtual.Slot.var s) delta;
      (* Compute offset of new slot and store to it. *)
      let* l = Context.Label.fresh in
      let* y = Context.Var.fresh in
      let+ word = Context.target >>| Target.word in
      let a = Insn.add y word (Virtual.Slot.var s) delta in
      let op' = Insn.replace_load_or_store_addr y op in
      [Insn.create ~label:l a; Insn.with_op i op']

  (* Rewrite an instruction. *)
  let rewrite_insn parts (m : scalars) (s : state) i =
    let open Context.Syntax in
    let op = Insn.op i in
    match Insn.load_or_store_to op with
    | None -> !![i]
    | Some (ptr, ty, ldst) ->
      if debug then
        Format.eprintf "%a: looking at %a.%a to %a\n%!"
          Label.pp (Insn.label i)
          pp_load_or_store ldst
          Type.pp_basic ty
          Var.pp ptr;
      match Map.find s ptr with
      | Some Top | None -> !![i]
      | Some Offset (base, off) ->
        match find_partition parts base off @@ basic_size ty with
        | Some p -> rewrite_insn_exact m i ~exact:p.off ~base ~off
        | None ->
          if debug then
            Format.eprintf "no parts found\n%!";
          !![i]

  let rewrite_with_partitions slots fn (s : solution) parts m =
    let open Context.Syntax in
    let* blks = Func.blks fn |> Context.Seq.map ~f:(fun b ->
        let s = ref @@ Solution.get s @@ Blk.label b in
        let+ insns = Blk.insns b |> Context.Seq.map ~f:(fun i ->
            let+ is = rewrite_insn parts m !s i in
            s := Analysis.transfer_op slots !s @@ Insn.op i; is)
          >>| List.concat @. Seq.to_list in
        Blk.with_insns b insns) >>| Seq.to_list in
    Context.lift_err @@ Func.with_blks fn blks

  let insert_new_slots fn m = Map.fold m ~init:fn
      ~f:(fun ~key:_ ~data fn -> Func.insert_slot fn data)

  let run fn =
    let open Context.Syntax in
    let slots = Analysis.collect_slots fn in
    if Map.is_empty slots then !!fn else
      let s = Analysis.analyze slots fn in
      let accs = collect_accesses slots fn s in
      let parts = partition_acesses accs in
      if debug then
        Map.iteri parts ~f:(fun ~key ~data ->
            Format.eprintf "partitions for %a:\n%!" Var.pp key;
            List.iter data ~f:(fun p ->
                Format.eprintf "  %a\n%!" pp_partition p));
      let* m = materialize_partitions slots parts in
      let fn = insert_new_slots fn m in
      rewrite_with_partitions slots fn s parts m
end
