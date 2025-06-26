open Core
open Regular.Std
open Pseudo

let (--) = Set.diff
let (++) = Set.union
let (&) = Set.inter

module Make(M : Machine_intf.S) = struct
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
    Label.Tree.to_sequence blks |>
    Seq.filter_map ~f:(fun (label, b) ->
        let insns, changed, _ =
          Blk.insns b ~rev:true |>
          Seq.fold ~init:([], false, Live.outs live label) ~f:insn in
        if changed then Some (Blk.create ~label ~insns)
        else None) |> Seq.to_list |> function
    | [] -> blks
    | bs ->
      let blks = List.fold bs ~init:blks ~f:(fun acc b ->
          Label.Tree.set acc ~key:(Blk.label b) ~data:b) in
      run ~keep blks cfg

  (* Set of registers that should always be live at the exit. *)
  let init_keep fn =
    let init = Rv.Set.singleton @@ Rv.reg M.Reg.sp in
    Func.rets fn |> Seq.map ~f:Rv.reg |> Seq.fold ~init ~f:Set.add

  let run fn =
    let keep = init_keep fn in
    let cfg = Cfg.create ~dests:M.Insn.dests fn in
    let blks = Func.map_of_blks fn in
    Func.update_blks' fn @@ run ~keep blks cfg
end
