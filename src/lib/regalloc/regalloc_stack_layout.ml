open Core
open Regular.Std
open Pseudo

module Slot = Virtual.Slot

module Make(M : Machine_intf.S)(C : Context_intf.S) = struct
  open C.Syntax

  module Rv = M.Regvar

  let alup i a = (i + a - 1) land -a

  let order_slots fn =
    Func.slots fn |> Seq.to_list |>
    List.sort ~compare:(fun a b ->
        (* Sort in descending order of size, then alignment. *)
        match Int.compare (Slot.size b) (Slot.size a) with
        | 0 -> Int.compare (Slot.align b) (Slot.align a)
        | n -> n)

  let compute_size = List.fold ~init:0 ~f:(fun o s ->
      let size = Slot.size s in
      let align = Slot.align s in
      alup o align + size)

  let compute_offsets slots start =
    List.fold slots ~init:(start, Var.Map.empty) ~f:(fun (o, m) s ->
        let v = Slot.var s in
        let size = Slot.size s in
        let align = Slot.align s in
        (* Round up the offset to the correct alignment. *)
        let o = alup o align in
        let m = Map.set m ~key:v ~data:o in
        o + size, m) |> snd

  let callee_saves fn =
    Func.blks fn |> Seq.fold ~init:Rv.Set.empty ~f:(fun acc b ->
        Blk.insns b |> Seq.fold ~init:acc ~f:(fun acc i ->
            let insn = Insn.insn i in
            let use = M.Insn.reads insn in
            let def = M.Insn.writes insn in
            Set.union use def |> Set.filter ~f:(fun rv ->
                match Rv.which rv with
                | First r -> M.Reg.is_callee_save r
                | Second _ -> false) |>
            Set.union acc)) |>
    Set.to_list |> List.map ~f:(fun rv ->
        match Rv.which rv with
        | First r -> r
        | Second _ -> assert false)

  let freshen = C.List.map ~f:(fun insn ->
      let+ label = C.Label.fresh in
      Insn.create ~label ~insn)

  let wordsz = Type.sizeof_imm_base (Target.word M.target) / 8

  let run fn =
    let dict = Func.dict fn in
    if not @@ Dict.mem dict Tags.stack_laid_out then
      let frame = Dict.mem dict Func.Tag.needs_stack_frame in
      let slots = order_slots fn in
      let size = compute_size slots in
      (* The frame pointer offsets will be negative. We're also accounting
         for the fact that the previous frame pointer will be preserved
         on the stack. *)
      let start = if frame then -(size + wordsz) else 0 in
      let offsets = compute_offsets slots start in
      let base = if frame then M.Reg.fp else M.Reg.sp in
      let fn = Func.map_blks fn ~f:(fun b ->
          Blk.map_insns b ~f:(fun i ->
              let insn = Insn.insn i in
              let insn' = M.Regalloc.assign_slots base offsets insn in
              Insn.with_insn i insn')) in
      (* Allocate the stack frame and preserve any callee-save registers. *)
      let regs = callee_saves fn in
      let entry = Func.entry fn in
      let prologue, epilogue = if frame
        then M.Regalloc.(frame_prologue, frame_epilogue)
        else M.Regalloc.(no_frame_prologue, no_frame_epilogue) in
      let* blks =
        Func.blks fn |> C.Seq.map ~f:(fun b ->
            let insns = Blk.insns b |> Seq.to_list in
            (* Insert prologue if this is the entry block. *)
            let* insns =
              if Blk.has_label b entry then
                let+ insns' = freshen @@ prologue regs size in
                insns' @ insns
              else !!insns in
            (* Insert epilogue if we see a return. *)
            let+ insns =
              C.List.map insns ~f:(fun i ->
                  let insn = Insn.insn i in
                  if M.Insn.is_return insn then
                    let+ insns = freshen @@ epilogue regs size in
                    insns @ [i]
                  else !![i])
              >>| List.concat in
            Blk.with_insns b insns)
        >>| Seq.to_list in
      (* Update the dict. *)
      let dict = Dict.remove dict Func.Tag.needs_stack_frame in
      let dict = Dict.set dict Tags.stack_laid_out () in
      C.lift_err @@ Func.create () ~dict ~blks
        ~slots:[] ~name:(Func.name fn)
        ~rets:(Func.rets fn |> Seq.to_list)
    else !!fn
end
