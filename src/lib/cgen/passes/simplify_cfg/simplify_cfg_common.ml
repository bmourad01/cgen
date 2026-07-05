open Core
open Virtual

module O = Cgen_utils.Monads.Option
module LT = Label.Dense_table
module LS = Label.Dense_set
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
  Func.blks fn |> Sequence.iter ~f:(fun b ->
      Blk.insns b |> Sequence.iter ~f:(fun i ->
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
  let dom = Semi_nca.compute cfg Label.pseudoentry in
  Func.blks fn |> Sequence.iter ~f:(fun b ->
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
  Sequence.filter ~f:not_pseudo |>
  Sequence.is_empty

let reverse_postorder cfg =
  let n = Cfg.number_of_nodes cfg in
  let vis = LS.create ~capacity:n () in
  let out = ref [] in
  let rec visit n =
    if LS.strict_add vis n then begin
      Sequence.iter (Cfg.Node.succs n cfg) ~f:visit;
      out := n :: !out
    end in
  Sequence.iter (Cfg.nodes cfg) ~f:visit;
  !out

(* Refresh the edges in the CFG and remove any blocks that
   are disjoint. *)
let recompute_cfg env fn =
  let g = Cfg.create fn in
  let fn, g' =
    reverse_postorder g |>
    List.fold ~init:(fn, g) ~f:(fun ((fn, g) as acc) l ->
        if is_disjoint env g l then
          let g' = Cfg.Node.remove l g in
          LT.remove env.blks l;
          Func.remove_blk_exn fn l, g'
        else acc) in
  env.dom <- Semi_nca.compute g' Label.pseudoentry;
  env.cfg <- g';
  fn

(* Remove the cases of the switch that have the same target and args
   as the default case. *)
let sw_hoist_default changed t i d tbl =
  Ctrl.Table.enum tbl |> Sequence.filter_map ~f:(fun ((_, l) as e) ->
      Option.some_if (not @@ equal_local d l) e) |>
  Sequence.to_list |> function
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
  Sequence.take s 2 |> Sequence.to_list |> function
  | [x] -> Some x
  | _ -> None
