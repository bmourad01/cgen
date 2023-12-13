(* Identify blocks with no instructions and a single `ret`. If there are
   duplicates, then an arbitrary block is chosen as the canonical element,
   and the rest are redirected to this block. *)

open Core
open Regular.Std
open Virtual
open Simplify_cfg_common

open O.Let

let find_loc tbl : local -> local option = function
  | `label (l, args) ->
    let+ l' = Hashtbl.find tbl l in
    `label (l', args)

let find_dst tbl : dst -> dst option = function
  | #local as l -> (find_loc tbl l :> dst option)
  | #global -> None

let map_dst changed tbl d = match find_dst tbl d with
  | Some x -> changed := true; x
  | None -> d

let map_loc changed tbl l = match find_loc tbl l with
  | Some x -> changed := true; x
  | None -> l

let map_blk changed tbl b =
  let dst = map_dst changed tbl in
  let loc = map_loc changed tbl in
  Blk.map_ctrl b ~f:(function
      | (`hlt | `ret _) as x -> x
      | `jmp d -> `jmp (dst d)
      | `br (c, y, n) ->
        let y = dst y in
        let n = dst n in
        if equal_dst y n
        then (changed := true; `jmp y)
        else `br (c, y, n)
      | `sw (t, i, d, tbl) ->
        let d = loc d in
        let tbl = Ctrl.Table.map_exn tbl ~f:(fun i l -> i, loc l) in
        sw_hoist_default changed t i d tbl)

let run env =
  let tbl = Label.Table.create () in
  let canon = Hashtbl.create (module struct
      type t = int * operand option [@@deriving compare, hash, sexp]
    end) in
  Hashtbl.iteri env.blks ~f:(fun ~key:l ~data:b ->
      if Seq.is_empty @@ Blk.insns b
      then match Blk.ctrl b with
        | `ret a ->
          let n = Seq.length @@ Blk.args b in
          Hashtbl.update canon (n, a) ~f:(function
              | Some l' -> Hashtbl.set tbl ~key:l ~data:l'; l'
              | None -> l)
        | _ -> ());
  let changed = ref false in
  if not @@ Hashtbl.is_empty tbl then
    Hashtbl.map_inplace env.blks ~f:(map_blk changed tbl);
  !changed
