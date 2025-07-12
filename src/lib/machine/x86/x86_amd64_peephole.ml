open Core
open Regular.Std
open Pseudo
open X86_amd64_common.Insn

module Rv = X86_amd64_common.Regvar

let decomp i = Insn.label i, Insn.insn i

let map_insns fn t =
  if Label.Tree.is_empty t then fn
  else Func.map_blks fn ~f:(fun b ->
      Blk.map_insns b ~f:(fun i ->
          match Label.Tree.find t @@ Insn.label i with
          | Some insn -> Insn.with_insn i insn
          | None -> i))

let filter_not_in fn t =
  if Label.Tree_set.is_empty t then fn
  else Func.map_blks fn ~f:(fun b ->
      Blk.insns b |> Seq.filter ~f:(fun i ->
          not @@ Label.Tree_set.mem t @@ Insn.label i) |>
      Seq.to_list |> Blk.with_insns b)

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
  Func.blks fn |> Seq.fold ~init:Label.Tree.empty ~f:(fun acc b ->
      Blk.label b |> Label.Tree.find afters |>
      Option.value_map ~default:acc ~f:(fun after ->
          Blk.insns b ~rev:true |> Seq.map ~f:decomp |>
          Fn.flip Seq.take 2 |> Seq.to_list |> function
          | [lb, JMP (Jlbl b); la, Jcc (cc, a)] when Label.(a = after) ->
            Label.Tree.set
              (Label.Tree.set acc ~key:la ~data:(Jcc (negate_cc cc, b)))
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
  Func.blks fn |> Seq.fold ~init:Label.Tree_set.empty ~f:(fun acc b ->
      Blk.label b |> Label.Tree.find afters |>
      Option.value_map ~default:acc ~f:(fun after ->
          Blk.insns b ~rev:true |>
          Seq.map ~f:decomp |> Seq.hd |> function
          | Some (la, JMP (Jlbl a)) when Label.(a = after) ->
            Label.Tree_set.add acc la
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
  Func.blks fn |> Seq.fold ~init:Label.Tree_set.empty ~f:(fun acc b ->
      let rec go acc s = match Seq.to_list @@ Seq.take s 2 with
        | [] | [_] -> acc
        | [l, Two (ADD, Oreg (r, `i64), Oimm _);
           _, LEAVE] when Rv.has_reg r `rsp ->
          let acc = Label.Tree_set.add acc l in
          go acc @@ Seq.drop_eagerly s 2
        | _ -> go acc @@ Seq.drop_eagerly s 1 in
      go acc @@ Seq.map ~f:decomp @@ Blk.insns b)

let dealloc_stack_before_leave fn =
  filter_not_in fn @@ collect_dealloc_stack_before_leave fn

let run fn =
  let afters = Func.collect_afters fn in
  let fn = invert_branches afters fn in
  let fn = implicit_fallthroughs afters fn in
  let fn = dealloc_stack_before_leave fn in
  fn
