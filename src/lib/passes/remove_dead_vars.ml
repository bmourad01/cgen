open Core
open Regular.Std
open Monads.Std
open Virtual

module E = Monad.Result.Error

let (@/) i s = not @@ Set.mem s i
let (--) = Var.Set.remove
let (++) = Var.Set.union
let noti s i _ = i @/ s

let map_loc unused : local -> local * bool = function
  | `label (l, args) as loc -> match Label.Tree.find unused l with
    | Some s -> `label (l, List.filteri args ~f:(noti s)), true
    | None -> loc, false

let map_dst unused : dst -> dst * bool = function
  | #local as l ->
    let l, changed = map_loc unused l in
    (l :> dst), changed
  | #global as g -> g, false

let map_tbl unused tbl =
  let changed = ref false in
  let tbl = Ctrl.Table.map_exn tbl ~f:(fun i l ->
      let l, c = map_loc unused l in
      changed := !changed || c;
      i, l) in
  tbl, !changed

let map_ctrl unused (c : ctrl) =
  let loc = map_loc unused in
  let dst = map_dst unused in
  match c with
  | `hlt -> `hlt, false
  | `jmp d ->
    let d, cd = dst d in
    `jmp d, cd
  | `br (c, y, n) ->
    let y, cy = dst y in
    let n, cn = dst n in
    `br (c, y, n), (cy || cn)
  | `ret _ as r -> r, false
  | `sw (t, i, d, tbl) ->
    let d, cd = loc d in
    let tbl, ct = map_tbl unused tbl in
    `sw (t, i, d, tbl), (cd || ct)
  | `tcall _ -> c, false

let collect_unused_args live blks =
  Seq.fold blks ~init:Label.Tree.empty ~f:(fun acc b ->
      let l = Blk.label b in
      let needed = Live.uses live l ++ Live.outs live l in
      let args =
        Blk.args b |> Seq.filter_mapi ~f:(fun i x ->
            Option.some_if (x @/ needed) i) |>
        Int.Set.of_sequence in
      if Set.is_empty args then acc
      else Label.Tree.set acc ~key:l ~data:args)

(* Even if the result of a div/rem may be unused, if the instruction has
   the potential to trap then removing it will change the semantics. *)
let check_div_rem i = match Insn.op i with
  | `bop (_, (`div #Type.imm | `udiv _ | `rem #Type.imm | `urem _), _, r) ->
    begin match r with
      | `int (i, _) -> Bv.(i = zero)
      | _ -> true
    end
  | _ -> false

let keep i x alive =
  Insn.is_effectful i ||
  Set.mem alive x ||
  check_div_rem i

let insn (acc, changed, alive) i = match Insn.lhs i with
  | Some x when not @@ keep i x alive -> acc, true, alive
  | Some x -> i :: acc, changed, alive -- x ++ Insn.free_vars i
  | None -> i :: acc, changed, alive ++ Insn.free_vars i

let remove_unused_slots fn live =
  let ins = Live.ins live @@ Func.entry fn in
  Func.slots fn |> Seq.fold ~init:fn ~f:(fun fn s ->
      let x = Func.Slot.var s in
      if Set.mem ins x then fn else Func.remove_slot fn x)

let rec run' fn =
  let live = Live.compute fn in
  let blks = Func.blks fn in
  let unused = collect_unused_args live blks in
  Seq.filter_map blks ~f:(fun b ->
      let label = Blk.label b in
      let ctrl, cc = map_ctrl unused @@ Blk.ctrl b in
      let args = Blk.args b in
      let args, ca = match Label.Tree.find unused label with
        | Some s -> Seq.filteri args ~f:(noti s), true
        | None -> args, false in
      let alive = Live.outs live label ++ Ctrl.free_vars ctrl in
      let insns, changed, _ =
        Blk.insns b ~rev:true |>
        Seq.fold ~init:([], ca || cc, alive) ~f:insn in
      if changed then
        Option.some @@ Blk.create () ~insns ~ctrl ~label
          ~args:(Seq.to_list args) ~dict:(Blk.dict b)
      else None) |> Seq.to_list |> function
  | [] -> remove_unused_slots fn live
  | blks -> run' @@ Func.update_blks fn blks

let run fn =
  if Dict.mem (Func.dict fn) Tags.ssa then
    Ok (run' fn)
  else
    E.failf "Expected SSA form for function %s"
      (Func.name fn) ()
