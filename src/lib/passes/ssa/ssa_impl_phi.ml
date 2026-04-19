open Core
open Regular.Std
open Ssa_impl_common

module Vset = Var.Tree_set
module Lset = Label.Tree_set
module Ltree = Label.Tree
module DF = Semi_nca.Frontier

(* First phase of the algorithm is to insert arguments to basic blocks
   and control-flow instructions based on the dominance frontier. *)
module Make(M : L) : sig
  val go : (M.Live.t, M.Cfg.t, M.Blk.t) env -> unit
end = struct
  open M

  type state = {
    defs : Lset.t VT.t;
    args : Var.t list LT.t;
    ctrl : Ctrl.t LT.t;
    outs : Var.t list Ltree.t LT.t;
  }

  let define defs d l = VT.update defs l ~f:(function
      | None -> Lset.singleton d
      | Some s -> Lset.add s d)

  let blocks_that_define_var st x =
    VT.find st.defs x |>
    Option.value ~default:Lset.empty

  let has_arg st l x =
    LT.find_exn st.args l |>
    Fn.flip List.mem x ~equal:Var.equal

  let init env =
    let nblks = LT.length env.blks in
    let defs = VT.create () in
    let args = LT.create ~capacity:nblks () in
    let ctrl = LT.create ~capacity:nblks () in
    let outs = LT.create ~capacity:nblks () in
    LT.iteri env.blks ~f:(fun ~key:l ~data:b ->
        LT.set ctrl ~key:l ~data:(Blk.ctrl b);
        (* Vars defined by existing block arguments. *)
        let args' = Seq.to_list @@ Blk.args b in
        LT.set args ~key:l ~data:args';
        List.iter args' ~f:(define defs l);
        (* Vars defined by instructions. *)
        Blk.insns b |> Seq.map ~f:Insn.lhs |>
        Seq.iter ~f:(List.iter ~f:(define defs l)));
    {defs; args; ctrl; outs}

  let update_incoming env l x outs =
    Cfg.Node.preds l env.cfg |> Seq.iter ~f:(fun l' ->
        LT.update outs l' ~f:(function
            | Some inc -> Ltree.add_multi inc ~key:l ~data:x
            | None -> Ltree.singleton l [x]))

  let add_arg env st l x =
    LT.add_multi st.args ~key:l ~data:x;
    update_incoming env l x st.outs

  let iterated_frontier f blks =
    let blks = Lset.add blks Label.pseudoentry in
    let df = Lset.fold ~init:Lset.empty ~f:(fun init b ->
        Lset.union init (DF.get f b)) in
    let rec fixpoint idf =
      let idf' = df @@ Lset.union idf blks in
      if Lset.equal idf idf' then idf' else fixpoint idf' in
    fixpoint Lset.empty

  let needs_arg env st l x =
    Vset.mem (Live.ins env.live l) x &&
    not (has_arg st l x)

  let insert_blk_args env st =
    Live.fold env.live ~init:Vset.empty
      ~f:(fun u _ v -> Vset.union u v) |>
    Vset.iter ~f:(fun x ->
        blocks_that_define_var st x |>
        iterated_frontier env.df |>
        Lset.iter ~f:(fun l ->
            if needs_arg env st l x
            then add_arg env st l x))

  let find_inc inc l = Ltree.find inc l |> Option.value ~default:[]

  let insert_ctrl_args st =
    LT.iteri st.outs ~f:(fun ~key:l ~data:inc ->
        if not @@ Label.is_pseudo l then
          LT.update st.ctrl l ~f:(function
              | Some c -> argify_ctrl ~inc:(find_inc inc) c
              | None -> assert false))

  let go env =
    let st = init env in
    insert_blk_args env st;
    insert_ctrl_args st;
    LT.map_inplace env.blks ~f:(fun b ->
        let label = Blk.label b in
        let dict = Blk.dict b in
        let args = LT.find_exn st.args label in
        let ctrl = LT.find_exn st.ctrl label in
        let insns = Blk.insns b |> Seq.to_list in
        Blk.create ~dict ~args ~insns ~ctrl ~label ())
end
