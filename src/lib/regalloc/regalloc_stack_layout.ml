open Core
open Regular.Std
open Pseudo

module Slot = Virtual.Slot

module Make(M : Machine_intf.S)(C : Context_intf.S) = struct
  open C.Syntax

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

  let run fn =
    let dict = Func.dict fn in
    let base, addend =
      if Dict.mem dict Func.Tag.needs_stack_frame then
        let word = Target.word M.target in
        M.Reg.fp, Type.sizeof_imm_base word / 8
      else M.Reg.sp, 0 in
    let _size, offsets = compute_offsets fn addend in
    let fn = Func.map_blks fn ~f:(fun b ->
        Blk.map_insns b ~f:(fun i ->
            Insn.insn i |>
            M.Regalloc.assign_slots base offsets |>
            Insn.with_insn i)) in
    let fn = Func.with_slots fn [] in
    let dict = Dict.remove dict Func.Tag.needs_stack_frame in
    let fn = Func.with_dict fn dict in
    !!fn
end
