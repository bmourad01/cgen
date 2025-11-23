(* Same as `Subst_mapper` with as much re-use as possible. *)

open Core
open Regular.Std
open Virtual
open Abi
open Subst_mapper

type t = operand Var.Map.t

let map_callarg subst : Insn.callarg -> Insn.callarg = function
  | `reg (a, r) -> `reg (map_arg subst a, r)
  | `stk (a, o) -> `stk (map_arg subst a, o)

let map_op subst (op : Insn.op) =
  let arg = map_arg subst in
  match op with
  | `bop (x, b, l, r) -> `bop (x, b, arg l, arg r)
  | `uop (x, u, a) -> `uop (x, u, arg a)
  | `sel (x, t, c, l, r) -> map_sel subst x t c l r
  | `call (x, f, args) ->
    let f = map_global subst f in
    let args = List.map args ~f:(map_callarg subst) in
    `call (x, f, args)
  | `load (x, t, a) -> `load (x, t, arg a)
  | `store (t, v, a) -> `store (t, arg v, arg a)
  | `regcopy _ -> op
  | `regstore (r, a) -> `regstore (r, arg a)
  | `regassign (r, a) -> `regassign (r, arg a)
  | `stkargs _ -> op

let map_insn subst i =
  Insn.with_op i @@ map_op subst @@ Insn.op i

let map_tbl_entry subst i l = i, map_local subst l

let map_sw subst t i d tbl =
  let d = map_local subst d in
  let tbl = Ctrl.Table.map_exn tbl ~f:(map_tbl_entry subst) in
  match i with
  | `sym _ -> `sw (t, i, d, tbl)
  | `var x -> match Map.find subst x with
    | Some (#Ctrl.swindex as i) -> `sw (t, i, d, tbl)
    | Some `int (i, _) ->
      let d = Ctrl.Table.find tbl i |> Option.value ~default:d in
      `jmp (d :> dst)
    | Some o -> invalid "sw" o
    | None -> `sw (t, i, d, tbl)

let map_ctrl subst : ctrl -> ctrl = function
  | `hlt -> `hlt
  | `jmp d -> `jmp (map_dst subst d)
  | `br (c, y, n) -> map_br subst c y n
  | `ret xs -> `ret (List.map xs ~f:(fun (r, a) -> r, map_arg subst a))
  | `sw (t, i, d, tbl) -> map_sw subst t i d tbl

let map_blk subst b =
  let insns = Blk.insns b |> Seq.map ~f:(map_insn subst) in
  Seq.to_list insns, map_ctrl subst (Blk.ctrl b)

(* TODO: should we enable more than just the `jmp` case? With
   `br` and `switch` we can have different applications of the
   substitution for the same destination. *)
let map_blk_args subst b l = match Blk.ctrl b with
  | `jmp `label (l', args) when Label.(l = l') ->
    Some (List.map args ~f:(map_arg subst))
  | _ -> None

let blk_extend subst b b' =
  Blk.label b' |> map_blk_args subst b |> Option.bind ~f:(fun args ->
      Blk.args b' |> Seq.to_list |> List.zip args |> function
      | Ok l -> Option.some @@ List.fold l ~init:subst
          ~f:(fun subst (o, x) -> Map.set subst ~key:x ~data:o)
      | Unequal_lengths -> None)
