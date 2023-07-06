open Core
open Regular.Std
open Virtual

let map_loc unused : local -> local * bool = function
  | `label (l, args) as loc -> match Label.Tree.find unused l with
    | None -> loc, false
    | Some s -> (* `s` should never be empty. *)
      let args = List.filteri args ~f:(fun i _ -> not @@ Set.mem s i) in
      `label (l, args), true

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

let rec run fn =
  let live = Live.compute fn in
  let blks = Func.blks fn in
  let unused_args =
    Seq.fold blks ~init:Label.Tree.empty ~f:(fun acc b ->
        let l = Blk.label b in
        let uses = Live.uses live l in
        let outs = Live.outs live l in
        let needed = Set.union uses outs in
        let args =
          Blk.args b |> Seq.filter_mapi ~f:(fun i (x, _) ->
              Option.some_if (not @@ Set.mem needed x) i) |>
          Int.Set.of_sequence in
        if Set.is_empty args then acc
        else Label.Tree.set acc ~key:l ~data:args) in
  Seq.filter_map blks ~f:(fun b ->
      let label = Blk.label b in
      let ctrl, cc = map_ctrl unused_args @@ Blk.ctrl b in
      let args, ca = match Label.Tree.find unused_args label with
        | None -> Blk.args b, false
        | Some s -> Blk.args b |> Seq.filteri ~f:(fun i _ ->
            not @@ Set.mem s i), true in
      let insns = Blk.insns b |> Seq.to_list in
      let outs = Live.outs live label in
      let iouts = Live.insns live label in
      let alive x l =
        Set.mem outs x ||
        Set.mem (Label.Tree.find_exn iouts l) x in
      let changed = ref (ca || cc) in
      let insns = List.filter insns ~f:(fun i -> match Insn.lhs i with
          | Some x when not @@ alive x @@ Insn.label i ->
            changed := true; false
          | Some _ | None -> true) in
      if !changed then
        Option.some @@ Blk.create () ~insns ~ctrl ~label
          ~args:(Seq.to_list args)
      else None) |> Seq.to_list |> function
  | [] -> fn (* No changes, so we're done. *)
  | blks -> run @@ Func.update_blks fn blks
