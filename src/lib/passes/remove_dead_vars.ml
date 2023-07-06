open Core
open Regular.Std
open Virtual

let rec run fn =
  let live = Live.compute fn in
  Func.blks fn |> Seq.filter_map ~f:(fun b ->
      let label = Blk.label b in
      let ctrl = Blk.ctrl b in
      let insns = Blk.insns b |> Seq.to_list in
      let outs = Live.outs live label in
      let iouts = Live.insns live label in
      let alive x l =
        Set.mem outs x ||
        Set.mem (Label.Tree.find_exn iouts l) x in
      let changed = ref false in
      let insns = List.filter insns ~f:(fun i -> match Insn.lhs i with
          | Some x when not @@ alive x @@ Insn.label i ->
            changed := true; false
          | Some _ | None -> true) in
      if !changed then
        Option.some @@ Blk.create ()
          ~args:(Blk.args b |> Seq.to_list)
          ~insns ~ctrl ~label
      else None) |> Seq.to_list |> function
  | [] -> fn (* No changes, so we're done. *)
  | blks -> run @@ Func.update_blks fn blks
