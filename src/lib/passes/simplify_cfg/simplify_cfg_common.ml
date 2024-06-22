open Core
open Monads.Std
open Regular.Std
open Graphlib.Std
open Virtual

module O = Monad.Option

type env = {
  blks        : blk Label.Table.t;
  typs        : Type.t Var.Table.t;
  flag        : Var.t Var.Table.t;
  start       : Label.t;
  mutable cfg : Cfg.t;
  mutable dom : Label.t tree;
  mutable ret : Label.t option;
}

let collect_flag fn =
  let flag = Var.Table.create () in
  Func.blks fn |> Seq.iter ~f:(fun b ->
      Blk.insns b |> Seq.iter ~f:(fun i ->
          match Insn.op i with
          | `uop (x, `flag _, `var y) ->
            Hashtbl.set flag ~key:x ~data:y;
          | _ -> ()));
  flag

let init fn =
  let cfg = Cfg.create fn in
  let start = Func.entry fn in
  let blks = Label.Table.create () in
  let typs = Var.Table.create () in
  let flag = collect_flag fn in
  let dom = Graphlib.dominators (module Cfg) cfg Label.pseudoentry in
  Func.blks fn |> Seq.iter ~f:(fun b ->
      Hashtbl.set blks ~key:(Blk.label b) ~data:b);
  {blks; typs; flag; start; cfg; dom; ret = None}

let is_ret env l = match env.ret with
  | Some l' -> Label.(l = l')
  | None -> false

let update_fn env fn =
  Func.blks fn |>
  Seq.fold ~init:[] ~f:(fun acc b ->
      let l = Blk.label b in
      if Hashtbl.mem env.blks l then acc
      else l :: acc) |>
  Func.remove_blks_exn fn |>
  Func.map_blks ~f:(fun b ->
      Hashtbl.find_exn env.blks @@ Blk.label b)

let not_pseudo = Fn.non Label.is_pseudo

let is_disjoint env cfg l =
  not_pseudo l &&
  Label.(l <> env.start) &&
  Cfg.Node.preds l cfg |>
  Seq.filter ~f:not_pseudo |>
  Seq.is_empty

(* Refresh the edges in the CFG and remove any blocks that
   are disjoint. *)
let recompute_cfg env fn =
  let g = Cfg.create fn in
  let fn, g', changed =
    Graphlib.reverse_postorder_traverse (module Cfg) g |>
    Seq.fold ~init:(fn, g, false) ~f:(fun ((fn, g, _) as acc) l ->
        if is_disjoint env g l then
          let g' = Cfg.Node.remove l g in
          Hashtbl.remove env.blks l;
          Func.remove_blk_exn fn l, g', true
        else acc) in
  if changed then begin
    env.dom <- Graphlib.dominators (module Cfg) g' Label.pseudoentry;
    env.cfg <- g'
  end;
  fn

(* Remove the cases of the switch that have the same target and args
   as the default case. *)
let sw_hoist_default changed t i d tbl =
  Ctrl.Table.enum tbl |> Seq.filter_map ~f:(fun ((_, l) as e) ->
      Option.some_if (not @@ equal_local d l) e) |>
  Seq.to_list |> function
  | [] ->
    changed := true;
    `jmp (d :> dst)
  | cs ->
    let tbl' = Ctrl.Table.create_exn cs t in
    let len' = Ctrl.Table.length tbl' in
    let len = Ctrl.Table.length tbl in
    if len' < len then changed := true;
    `sw (t, i, d, tbl')
