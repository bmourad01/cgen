(* Merge all `ret` instructions to a single block. *)

open Core
open Virtual
open Simplify_cfg_common

open Context.Syntax

let map_blk tbl rb b = match Hashtbl.find tbl @@ Blk.label b with
  | Some (Some a) ->
    Blk.with_ctrl b @@ `jmp (`label (Blk.label rb, [a]))
  | Some None ->
    Blk.with_ctrl b @@ `jmp (`label (Blk.label rb, []))
  | None -> b

let commit env tbl rb fn =
  let key = Blk.label rb in
  Hashtbl.map_inplace env.blks ~f:(map_blk tbl rb);
  Hashtbl.set env.blks ~key ~data:rb;
  env.ret <- Some key;
  recompute_cfg env @@
  Fn.flip Func.insert_blk rb @@
  update_fn env fn

let run env fn =
  let tbl = Label.Table.create () in
  Hashtbl.iteri env.blks
    ~f:(fun ~key:l ~data:b -> match Blk.ctrl b with
        | `ret a -> Hashtbl.set tbl ~key:l ~data:a
        | _ -> ());
  if Hashtbl.length tbl <= 1 then !!fn
  else match snd @@ Hashtbl.choose_exn tbl with
    | Some _ ->      
      let* r = Context.Var.fresh in
      let ctrl = `ret (Some (`var r)) in
      let+ rb = Context.Virtual.blk ~args:[r] ~ctrl () in
      commit env tbl rb fn
    | None ->
      let+ rb = Context.Virtual.blk ~ctrl:(`ret None) () in
      commit env tbl rb fn
