open Core
open Regular.Std
open Pseudo

let (--) = Set.diff
let (++) = Set.union
let (&) = Set.inter

module Make(M : Machine_intf.S_insn) = struct
  module Live = Pseudo_live.Make(M)
  module Rv = M.Regvar

  let should_keep i w alive =
    M.Insn.always_live i ||
    not (Set.is_empty (alive & w))

  (* For debugging. *)
  let pp_insn ppf (desc, r, w, alive) =
    let pp_sep ppf () = Format.fprintf ppf ", " in
    Format.fprintf ppf "%a: (r = (%a)), (w = (%a)), (alive = (%a))"
      (Insn.pp M.Insn.pp) desc
      (Format.pp_print_list ~pp_sep Rv.pp)
      (Set.to_list r)
      (Format.pp_print_list ~pp_sep Rv.pp)
      (Set.to_list w)
      (Format.pp_print_list ~pp_sep Rv.pp)
      (Set.to_list alive)

  let insn (acc, changed, alive) desc =
    let i = Insn.insn desc in
    let r = M.Insn.reads i in
    let w = M.Insn.writes i in
    let alive' = alive -- w ++ r in
    let acc, changed =
      if should_keep i w alive
      then desc :: acc, changed
      else acc, true in
    acc, changed, alive'

  let rec run ~keep blks cfg =
    let live = Live.compute' ~keep cfg blks in
    Label.Tree.fold blks ~init:[] ~f:(fun ~key:label ~data:b acc ->
        let insns, changed, _ =
          Blk.fold_insns b ~rev:true ~f:insn
            ~init:([], false, Live.outs live label) in
        if changed then Blk.create ~label ~insns :: acc
        else acc) |> function
    | [] -> blks
    | bs ->
      let blks = List.fold bs ~init:blks ~f:(fun acc b ->
          Label.Tree.set acc ~key:(Blk.label b) ~data:b) in
      run ~keep blks cfg

  (* Set of registers that should always be live at the exit. *)
  let init_keep fn =
    let init = Rv.Set.singleton @@ Rv.reg M.Reg.sp in
    Func.fold_rets fn ~init ~f:(fun acc r -> Set.add acc (Rv.reg r))

  let run fn =
    let keep = init_keep fn in
    let cfg = Cfg.create fn
        ~is_barrier:M.Insn.is_barrier
        ~is_pseudo:M.Insn.is_pseudo
        ~dests:M.Insn.dests in
    let blks = Func.map_of_blks fn in
    Func.update_blks' fn @@ run ~keep blks cfg
end
