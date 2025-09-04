open Core
open Regular.Std
open Graphlib.Std
open Pseudo
open X86_amd64_common.Insn

module Rv = X86_amd64_common.Regvar
module Ltree = Label.Tree
module Lset = Label.Tree_set

let decomp i = Insn.label i, Insn.insn i

let map_insns fn t =
  if Ltree.is_empty t then fn
  else Func.map_blks fn ~f:(fun b ->
      Blk.map_insns b ~f:(fun i ->
          match Ltree.find t @@ Insn.label i with
          | Some insn -> Insn.with_insn i insn
          | None -> i))

let filter_not_in fn t =
  if Lset.is_empty t then fn
  else Func.map_blks fn ~f:(fun b ->
      Blk.insns b |> Seq.filter ~f:(fun i ->
          not @@ Lset.mem t @@ Insn.label i) |>
      Seq.to_list |> Blk.with_insns b)

(* Blocks that consist of a single instruction of the form:

   @label:
     jmp @otherlabel
*)
let collect_singles fn =
  let start = Func.start fn in
  Func.blks fn |> Seq.fold ~init:Ltree.empty ~f:(fun acc b ->
      let key = Blk.label b in
      if Label.(key = start) then acc
      else
        let is = Seq.map ~f:Insn.insn @@ Blk.insns b in
        match Seq.next is with
        | Some (JMP (Jlbl dst), rest) ->
          begin match Seq.next rest with
            | Some _ -> acc
            | None -> Ltree.set acc ~key ~data:dst
          end
        | _ -> acc)

(* Union-find with path compression. *)
let find_with_compression m l =
  let parent l = Ltree.find !m l |> Option.value ~default:l in
  let l = ref l in
  let p = ref @@ parent !l in
  while Label.(!l <> !p) do
    let g = parent !p in
    if Label.(g <> !p) then begin
      m := Ltree.set !m ~key:!l ~data:g;
      p := parent g
    end;
    l := g
  done;
  !p

(* For blocks collected in the above analysis, thread them through to
   the final destination.

   Example:

   @1:
     ...
     jmp @2
   @2:
     jmp @3
   @3:
     ...

   becomes

   @1:
     ...
     jmp @3
   @2:        <--- if nobody references this block anymore, it can be removed
     jmp @3
   @3:
     ...
*)
let jump_threading fn =
  let singles = collect_singles fn in
  if not @@ Label.Tree.is_empty singles then
    let find = find_with_compression @@ ref singles in
    Func.map_blks fn ~f:(fun b ->
        Blk.map_insns b ~f:(fun i ->
            Insn.with_insn i @@ match Insn.insn i with
            | Jcc (cc, dst) -> Jcc (cc, find dst)
            | JMP (Jlbl dst) -> JMP (Jlbl (find dst))
            | JMPtbl (d, ls) -> JMPtbl (find d, List.map ls ~f:find)
            | insn -> insn))
  else fn

(* Remove blocks that are not reachable from the entry block. *)
let remove_disjoint fn =
  let reachable = with_return @@ fun {return} ->
    let cfg = Cfg.create ~is_barrier ~dests fn in
    let start = Func.entry fn in
    Graphlib.depth_first_search (module Cfg) cfg ~start
      ~init:Lset.empty
      ~start_tree:(fun n s ->
          if Label.(n = start) then s else return s)
      ~enter_node:(fun _ n s -> Lset.add s n) in
  Func.blks fn |> Seq.map ~f:Blk.label |>
  Seq.filter ~f:(Fn.non @@ Lset.mem reachable) |>
  Seq.to_list |> Func.remove_blks_exn fn

(* Invert conditional branches based on the block layout.

   Example:

   @1:
     ...
     jne @2
     jmp @3
   @2:
     ...
   @3:
     ...

   becomes

   @1:
     ...
     je @3
     jmp @2  <--- this jump can now be turned into a fallthrough later
   @2:
     ...
   @3:
     ...
*)
let collect_invert_branches afters fn =
  Func.blks fn |> Seq.fold ~init:Ltree.empty ~f:(fun acc b ->
      Blk.label b |> Ltree.find afters |>
      Option.value_map ~default:acc ~f:(fun after ->
          Blk.insns b ~rev:true |> Seq.map ~f:decomp |>
          Fn.flip Seq.take 2 |> Seq.to_list |> function
          | [lb, JMP (Jlbl b); la, Jcc (cc, a)] when Label.(a = after) ->
            Ltree.set
              (Ltree.set acc ~key:la ~data:(Jcc (negate_cc cc, b)))
              ~key:lb ~data:(JMP (Jlbl a))
          | _ -> acc))

let invert_branches afters fn =
  map_insns fn @@ collect_invert_branches afters fn

(* Eliminate useless unconditional jumps where a fallthrough would suffice.

   Example:

   @1:
     ...
     jmp @2
   @2:
     ...

   becomes

   @1:
     ...
   @2:     <--- block @1 implicitly falls through to block @2
     ...
*)
let collect_implicit_fallthroughs afters fn =
  Func.blks fn |> Seq.fold ~init:Lset.empty ~f:(fun acc b ->
      Blk.label b |> Ltree.find afters |>
      Option.value_map ~default:acc ~f:(fun after ->
          Blk.insns b ~rev:true |>
          Seq.map ~f:decomp |> Seq.hd |> function
          | Some (la, JMP (Jlbl a)) when Label.(a = after) ->
            Lset.add acc la
          | _ -> acc))

let implicit_fallthroughs afters fn =
  filter_not_in fn @@ collect_implicit_fallthroughs afters fn

(* Deallocating the stack pointer followed by a LEAVE instruction
   is redundant.

   Example:

   @1:
     ...
     call $foo         <--- $foo takes arguments on the stack
     add rsp, 0x10_l   <--- space for stack args is cleaned up
     leave             <--- restore stack pointer and return
     ret

   becomes

   @1:
     call $foo
     leave
     ret

   because LEAVE will overwrite RSP anyway
*)
let collect_dealloc_stack_before_leave fn =
  Func.blks fn |> Seq.fold ~init:Lset.empty ~f:(fun acc b ->
      let rec go acc s = match Seq.to_list @@ Seq.take s 2 with
        | [] | [_] -> acc
        | [l, Two (ADD, Oreg (r, `i64), Oimm _);
           _, LEAVE] when Rv.has_reg r `rsp ->
          let acc = Lset.add acc l in
          go acc @@ Seq.drop_eagerly s 2
        | _ -> go acc @@ Seq.drop_eagerly s 1 in
      go acc @@ Seq.map ~f:decomp @@ Blk.insns b)

let dealloc_stack_before_leave fn =
  filter_not_in fn @@ collect_dealloc_stack_before_leave fn

let collect_redundant_spill_after_reload fn =
  Func.blks fn |> Seq.fold ~init:Lset.empty ~f:(fun acc b ->
      let rec go acc s = match Seq.to_list @@ Seq.take s 2 with
        | [] | [_] -> acc
        | [_, Two (MOV, Oreg (r2, _), Omem (a2, t2));
           l, Two (MOV, Omem (a1, t1), Oreg (r1, _))]
          when equal_amode a1 a2
            && equal_memty t1 t2
            && Rv.equal r1 r2 ->
          let acc = Lset.add acc l in
          go acc @@ Seq.drop_eagerly s 2
        | _ -> go acc @@ Seq.drop_eagerly s 1 in
      go acc @@ Seq.map ~f:decomp @@ Blk.insns b)

let redundant_spill_after_reload fn =
  filter_not_in fn @@ collect_redundant_spill_after_reload fn

(* If we have a LEA of the same address as a subsequent load,
   then use the result of the LEA as the address for the load.

   This is made under the assumption that the result of the LEA
   is going to be re-used later (otherwise it would have been
   recognized as dead code).
*)
let collect_reuse_lea fn =
  Func.blks fn |> Seq.fold ~init:Ltree.empty ~f:(fun acc b ->
      let rec go acc s = match Seq.to_list @@ Seq.take s 2 with
        | [] | [_] -> acc
        | [_, Two (LEA, Oreg (r1, _), Omem (a1, _));
           l, Two (MOV, Oreg (r2, r2t), Omem (a2, t2))]
          when equal_amode a1 a2 ->
          let data = Two (MOV, Oreg (r2, r2t), Omem (Ab r1, t2)) in
          let acc = Ltree.set acc ~key:l ~data in
          go acc @@ Seq.drop_eagerly s 2
        | _ -> go acc @@ Seq.drop_eagerly s 1 in
      go acc @@ Seq.map ~f:decomp @@ Blk.insns b)

let reuse_lea fn =
  map_insns fn @@ collect_reuse_lea fn

let run fn =
  let fn = jump_threading fn in
  let fn = remove_disjoint fn in
  let afters = Func.collect_afters fn in
  let fn = invert_branches afters fn in
  let fn = implicit_fallthroughs afters fn in
  let fn = dealloc_stack_before_leave fn in
  let fn = redundant_spill_after_reload fn in
  let fn = reuse_lea fn in
  fn
