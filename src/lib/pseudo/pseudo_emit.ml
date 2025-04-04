open Core
open Regular.Std

module Insn = Pseudo_insn
module Blk = Pseudo_blk
module Func = Pseudo_func
module Module = Pseudo_module

module Make(M : Machine_intf.S) = struct
  let emit ppf m =
    M.Emit.emit_prelude ppf @@ Module.name m;
    Module.data m |> Seq.iter ~f:(M.Emit.emit_data ppf);
    Module.funs m |> Seq.iter ~f:(fun fn ->
        M.Emit.emit_func ppf (Func.name fn, Func.linkage fn);
        Func.blks fn |> Seq.iter ~f:(fun b ->
            M.Emit.emit_blk ppf @@ Blk.label b;
            Blk.insns b |> Seq.iter ~f:(fun i ->
                M.Emit.emit_insn ppf @@ Insn.insn i)))
end
