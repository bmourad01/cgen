open Core
open Regular.Std
open Virtual

let run fn =
  let live = Live.compute fn in
  Func.blks fn |> Seq.filter_map ~f:(fun b ->
      let label = Blk.label b in
      let insns = Blk.insns b in
      let ctrl = Blk.ctrl b in
      let cvs = Ctrl.free_vars ctrl in
      let outs = Live.outs live label in
      let free = Seq.fold insns ~init:Label.Map.empty ~f:(fun m i ->
          Map.set m ~key:(Insn.label i) ~data:(Insn.free_vars i)) in
      let alive x rest =
        Set.mem outs x ||
        Set.mem cvs  x ||
        List.exists rest ~f:(fun i ->
            Set.mem (Map.find_exn free (Insn.label i)) x) in
      let changed = ref false in
      let rec filter acc = function
        | [] -> List.rev acc
        | i :: rest ->
          let acc = match Insn.lhs i with
            | Some x when not @@ alive x rest ->
              changed := true; acc
            | Some _ | None -> i :: acc in
          filter acc rest in
      let insns = filter [] @@ Seq.to_list insns in
      if !changed then
        Option.some @@ Blk.create ()
          ~args:(Blk.args b |> Seq.to_list)
          ~insns ~ctrl ~label
      else None) |>
  Seq.to_list |> Func.update_blks fn
