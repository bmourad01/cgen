open Core
open Regular.Std

module Insn = Pseudo_insn
module Blk = Pseudo_blk
module Func = Pseudo_func
module Module = Pseudo_module

module Make(M : Machine_intf.S) = struct
  let emit ppf m =
    let funs = Module.funs m |> Seq.to_list in
    let data = Module.data m |> Seq.to_list in
    let last_fun = List.length funs - 1 in
    let last_data = List.length data - 1 in
    M.Emit.emit_prelude ppf @@ Module.name m;
    if last_data >= 0 || last_fun >= 0 then
      M.Emit.emit_separator ppf ();
    List.iteri data ~f:(fun i d ->
        M.Emit.emit_data ppf d;
        if i < last_data then
          M.Emit.emit_separator ppf ());
    if last_data >= 0 && last_fun >= 0 then
      M.Emit.emit_separator ppf ();
    List.iteri funs ~f:(fun i fn ->
        let lnk = Func.linkage fn in
        let section = Linkage.section lnk in
        M.Emit.emit_func ppf (Func.name fn, lnk);
        Func.blks fn |> Seq.iter ~f:(fun b ->
            M.Emit.emit_blk ppf @@ Blk.label b;
            Blk.insns b |> Seq.iter ~f:(fun i ->
                let insn = Insn.insn i in
                let label = Insn.label i in
                M.Emit.emit_insn ppf (label, insn, section)));
        if i < last_fun then
          M.Emit.emit_separator ppf ())
end
