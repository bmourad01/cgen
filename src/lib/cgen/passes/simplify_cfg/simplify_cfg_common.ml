open Core
open Monads.Std
open Regular.Std
open Graphlib.Std
open Virtual

module O = Monad.Option
module LT = Label.Dense_table
module VT = Var.Dense_table

type env = {
  blks          : blk LT.t;
  typs          : Type.t VT.t;
  flag          : Var.t VT.t;
  mutable start : Label.t;
  mutable cfg   : Cfg.t;
  mutable dom   : Semi_nca.tree;
  mutable ret   : Label.t option;
}

let collect_flag fn =
  let flag = VT.create () in
  Func.blks fn |> Seq.iter ~f:(fun b ->
      Blk.insns b |> Seq.iter ~f:(fun i ->
          match Insn.op i with
          | `uop (x, `flag _, `var y) ->
            VT.set flag ~key:x ~data:y;
          | _ -> ()));
  flag

let init fn =
  let cfg = Cfg.create fn in
  let start = Func.entry fn in
  let blks = LT.create ~capacity:(Func.num_blks fn) () in
  let typs = VT.create () in
  let flag = collect_flag fn in
  let dom = Semi_nca.compute (module Cfg) cfg Label.pseudoentry in
  Func.blks fn |> Seq.iter ~f:(fun b ->
      LT.set blks ~key:(Blk.label b) ~data:b);
  {blks; typs; flag; start; cfg; dom; ret = None}

let is_ret env l = match env.ret with
  | Some l' -> Label.(l = l')
  | None -> false

let update_fn env fn =
  Func.filter_map_blks_exn fn ~f:(fun b ->
      LT.find env.blks @@ Blk.label b)

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
  let fn, g' =
    Graphlib.reverse_postorder_traverse (module Cfg) g |>
    Seq.fold ~init:(fn, g) ~f:(fun ((fn, g) as acc) l ->
        if is_disjoint env g l then
          let g' = Cfg.Node.remove l g in
          LT.remove env.blks l;
          Func.remove_blk_exn fn l, g'
        else acc) in
  env.dom <- Semi_nca.compute (module Cfg) g' Label.pseudoentry;
  env.cfg <- g';
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

let take_seq_singleton s =
  Seq.take s 2 |> Seq.to_list |> function
  | [x] -> Some x
  | _ -> None
