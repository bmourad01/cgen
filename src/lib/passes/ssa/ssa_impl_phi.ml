open Core
open Regular.Std
open Graphlib.Std
open Ssa_impl_common

(* First phase of the algorithm is to insert arguments to basic blocks
   and control-flow instructions based on the dominance frontier. *)
module Make(M : L) : sig
  val go : (M.Live.t, M.Cfg.t, M.Blk.t) env -> unit
end = struct
  open M

  type state = {
    defs : Label.Set.t Var.Table.t;
    args : Var.t list Label.Table.t;
    ctrl : Ctrl.t Label.Table.t;
    outs : Var.t list Label.Tree.t Label.Table.t;
  }

  let define defs l = Hashtbl.update defs ~f:(function
      | None -> Label.Set.singleton l
      | Some s -> Set.add s l)

  let blocks_that_define_var st x =
    Hashtbl.find st.defs x |>
    Option.value ~default:Label.Set.empty

  let has_arg st l x =
    Hashtbl.find_exn st.args l |>
    Fn.flip List.mem x ~equal:Var.equal

  let init env =
    let defs = Var.Table.create () in
    let args = Label.Table.create () in
    let ctrl = Label.Table.create () in
    let outs = Label.Table.create () in
    Hashtbl.iteri env.blks ~f:(fun ~key:l ~data:b ->
        Hashtbl.set ctrl ~key:l ~data:(Blk.ctrl b);
        (* Vars defined by existing block arguments. *)
        let args' = Seq.to_list @@ Blk.args b in
        Hashtbl.set args ~key:l ~data:args';
        List.iter args' ~f:(define defs l);
        (* Vars defined by instructions. *)
        Blk.insns b |> Seq.map ~f:Insn.lhs |>
        Seq.iter ~f:(List.iter ~f:(define defs l)));
    {defs; args; ctrl; outs}

  let update_incoming env l x outs =
    Cfg.Node.preds l env.cfg |> Seq.iter ~f:(fun l' ->
        Hashtbl.update outs l' ~f:(function
            | Some inc -> Label.Tree.add_multi inc ~key:l ~data:x
            | None -> Label.Tree.singleton l [x]))

  let add_arg env st l x =
    Hashtbl.add_multi st.args ~key:l ~data:x;
    update_incoming env l x st.outs

  let iterated_frontier f blks =
    let blks = Set.add blks Label.pseudoentry in
    let df = Set.fold ~init:Label.Set.empty ~f:(fun init b ->
        Frontier.enum f b |> Seq.fold ~init ~f:Set.add) in
    let rec fixpoint idf =
      let idf' = df @@ Set.union idf blks in
      if Set.equal idf idf' then idf' else fixpoint idf' in
    fixpoint Label.Set.empty

  let needs_arg env st l x =
    Set.mem (Live.ins env.live l) x &&
    not (has_arg st l x)

  let insert_blk_args env st =
    Live.fold env.live ~init:Var.Set.empty
      ~f:(fun u _ v -> Set.union u v) |>
    Set.iter ~f:(fun x ->
        blocks_that_define_var st x |>
        iterated_frontier env.df |>
        Set.iter ~f:(fun l ->
            if needs_arg env st l x
            then add_arg env st l x))

  let find_inc inc l =
    Label.Tree.find inc l |>
    Option.value ~default:[]

  let insert_ctrl_args st =
    Hashtbl.iteri st.outs ~f:(fun ~key:l ~data:inc ->
        if not @@ Label.is_pseudo l then
          Hashtbl.update st.ctrl l ~f:(function
              | Some c -> argify_ctrl ~inc:(find_inc inc) c
              | None -> assert false))

  let go env =
    let st = init env in
    insert_blk_args env st;
    insert_ctrl_args st;
    Hashtbl.map_inplace env.blks ~f:(fun b ->
        let label = Blk.label b in
        let dict = Blk.dict b in
        let args = Hashtbl.find_exn st.args label in
        let ctrl = Hashtbl.find_exn st.ctrl label in
        let insns = Blk.insns b |> Seq.to_list in
        Blk.create ~dict ~args ~insns ~ctrl ~label ())
end
