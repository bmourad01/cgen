open Core
open Regular.Std
open Pseudo
open X86_amd64_common.Insn

let decomp i = Insn.label i, Insn.insn i

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
  let t = collect_invert_branches afters fn in
  Func.map_blks fn ~f:(fun b ->
      Blk.map_insns b ~f:(fun i ->
          match Label.Tree.find t @@ Insn.label i with
          | Some insn -> Insn.with_insn i insn
          | None -> i))

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
  let t = collect_implicit_fallthroughs afters fn in
  Func.map_blks fn ~f:(fun b ->
      Blk.insns b |> Seq.filter ~f:(fun i ->
          not @@ Label.Tree_set.mem t @@ Insn.label i) |>
      Seq.to_list |> Blk.with_insns b)

let run fn =
  let afters = Func.collect_afters fn in
  let fn = invert_branches afters fn in
  let fn = implicit_fallthroughs afters fn in
  let dict = Func.dict fn in
  let dict = Dict.set dict Tags.peephole () in
  Func.with_dict fn dict
