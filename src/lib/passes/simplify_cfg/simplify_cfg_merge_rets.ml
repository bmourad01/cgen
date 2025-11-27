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
  Logs.debug (fun m ->
      m "%s: merged returns to new block %a: %s%!"
        __FUNCTION__ Label.pp key
        (Hashtbl.keys tbl |> List.to_string ~f:Label.to_string));
  Hashtbl.map_inplace env.blks ~f:(map_blk tbl rb);
  Hashtbl.set env.blks ~key ~data:rb;
  env.ret <- Some key;
  recompute_cfg env @@
  Fn.flip Func.insert_blk rb @@
  update_fn env fn

let map_retty fn tenv = function
  | #Type.basic as t -> (t :> Type.t)
  | `si8 -> `i8
  | `si16 -> `i16
  | `si32 -> `i32
  | `name s -> match Typecheck.Env.typeof_typ s tenv with
    | Ok t -> (t :> Type.t)
    | Error err ->
      failwithf "in function $%s: %s"
        (Func.name fn) (Error.to_string_hum err) ()

let run tenv env fn =
  let tbl = Label.Table.create () in
  Hashtbl.iteri env.blks
    ~f:(fun ~key:l ~data:b -> match Blk.ctrl b with
        | `ret a -> Hashtbl.set tbl ~key:l ~data:a
        | _ -> ());
  if Hashtbl.length tbl <= 1 then !!fn
  else match Func.return fn with
    | Some ty ->
      let data = map_retty fn tenv ty in
      let* r = Context.Var.fresh in
      Hashtbl.set env.typs ~key:r ~data;
      let ctrl = `ret (Some (`var r)) in
      let+ rb = Context.Virtual.blk ~args:[r] ~ctrl () in
      commit env tbl rb fn
    | None ->
      let+ rb = Context.Virtual.blk ~ctrl:(`ret None) () in
      commit env tbl rb fn
