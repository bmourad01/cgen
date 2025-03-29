open Core
open Regular.Std
open Pseudo

module Slot = Virtual.Slot

module Make(M : Machine_intf.S)(C : Context_intf.S) = struct
  open C.Syntax

  module Rv = M.Regvar

  let compute_offsets fn addend =
    Func.slots fn |> Seq.to_list |>
    List.sort ~compare:(fun a b ->
        (* Sort in descending order of size, then alignment. *)
        match Int.compare (Slot.size b) (Slot.size a) with
        | 0 -> Int.compare (Slot.align b) (Slot.align a)
        | n -> n) |>
    List.fold ~init:(addend, Var.Map.empty) ~f:(fun (o, m) s ->
        let v = Slot.var s in
        let size = Slot.size s in
        let align = Slot.align s in
        (* Round up the offset to the correct alignment. *)
        let o = (o + align - 1) land -align in
        let m = Map.set m ~key:v ~data:o in
        o + size, m)

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

  let run fn =
    let dict = Func.dict fn in
    let frame = Dict.mem dict Func.Tag.needs_stack_frame in
    (* Initial offset. *)
    let base, addend = if frame then
        let word = Target.word M.target in
        M.Reg.fp, Type.sizeof_imm_base word / 8
      else M.Reg.sp, 0 in
    (* Choose offsets for the slots. *)
    let size, offsets = compute_offsets fn addend in
    let fn = Func.map_blks fn ~f:(fun b ->
        Blk.map_insns b ~f:(fun i ->
            Insn.insn i |>
            M.Regalloc.assign_slots base offsets |>
            Insn.with_insn i)) in
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
    let dict = Dict.remove dict Func.Tag.needs_stack_frame in
    C.lift_err @@ Func.create () ~dict ~blks
      ~slots:[] ~name:(Func.name fn)
      ~rets:(Func.rets fn |> Seq.to_list)
end
