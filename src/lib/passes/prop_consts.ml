open Core
open Monads.Std
open Regular.Std
open Virtual

module E = Monad.Result.Error

open E.Let

let run fn =
  let* ctx = Expression.init fn in
  let* () = Expression.fill ctx in
  Expression.eval_all ctx;
  let blks = Func.blks fn in
  let insns = Label.Table.create () in
  let ctrls = Label.Table.create () in
  let unseen l = not (Hashtbl.mem insns l || Hashtbl.mem ctrls l) in
  let update env =
    Expression.Reify.enum env |>
    Seq.filter ~f:(fun (l, _) -> unseen l) |>
    Seq.iter ~f:(function
        | l, `insn o -> Hashtbl.set insns ~key:l ~data:o
        | l, `ctrl c -> Hashtbl.set ctrls ~key:l ~data:c) in
  let* () = E.Seq.iter blks ~f:(fun b ->
      let l = Blk.label b in
      let+ env = Expression.reify ctx l in
      update env) in
  let+ () = E.Seq.iter blks ~f:(fun b ->
      Blk.insns b |> E.Seq.iter ~f:(fun i ->
          let l = Insn.label i in
          if unseen l then
            let+ env = Expression.reify ctx l in
            update env
          else Ok ())) in
  Seq.map blks ~f:(fun b ->
      let label = Blk.label b in
      let args = Blk.args b |> Seq.to_list in
      let insns =
        Blk.insns b |> Seq.map ~f:(fun i ->
            let label = Insn.label i in
            Hashtbl.find insns label |>
            Option.value_map ~default:i ~f:(Insn.create ~label)) |>
        Seq.to_list in
      let ctrl = match Hashtbl.find ctrls label with
        | None -> Blk.ctrl b
        | Some c -> c in
      Blk.create ~args ~insns ~ctrl ~label ()) |>
  Seq.to_list |> Func.update_blks fn
