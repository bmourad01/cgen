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
        let lnk = Func.linkage fn in
        let section = Linkage.section lnk in
        M.Emit.emit_func ppf (Func.name fn, lnk);
        Func.blks fn |> Seq.iter ~f:(fun b ->
            M.Emit.emit_blk ppf @@ Blk.label b;
            Blk.insns b |> Seq.iter ~f:(fun i ->
                let insn = Insn.insn i in
                let label = Insn.label i in
                M.Emit.emit_insn ppf (label, insn, section))))
end
