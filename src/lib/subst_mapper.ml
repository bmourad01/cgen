(* This is fairly common enough to be shared by many passes. *)

open Core
open Regular.Std
open Virtual

type t = operand Var.Map.t

let invalid ctx o =
  let s = Format.asprintf "%a" pp_operand o in
  failwithf "Invalid %s operand %s" ctx s ()

let map_arg subst (o : operand) = match o with
  | `var x -> Map.find subst x |> Option.value ~default:o
  | _ -> o

let map_local subst : local -> local = function
  | `label (_, []) as l -> l
  | `label (l, args) ->
    `label (l, List.map args ~f:(map_arg subst))

let map_global (subst : t) (g : global) = match g with
  | `addr _ | `sym _ -> g
  | `var x -> match Map.find subst x with
    | Some `int (i, _) -> `addr i
    | Some (`sym _ as s) -> s
    | Some (`var _ as x) -> x
    | Some o -> invalid "global" o
    | None -> g

let map_dst subst (d : dst) = match d with
  | #global as g ->
    let g = map_global subst g in
    (g :> dst)
  | #local as l ->
    let l = map_local subst l in
    (l :> dst)

let map_sel subst x t c l r =
  let arg = map_arg subst in
  match Map.find subst c with
  | Some `bool true -> `uop (x, `copy t, arg l)
  | Some `bool false -> `uop (x, `copy t, arg r)
  | Some `var c -> `sel (x, t, c, arg l, arg r)
  | Some o -> invalid "sel" o
  | None -> `sel (x, t, c, arg l, arg r)

let map_op subst (op : Insn.op) =
  let arg = map_arg subst in
  match op with
  | `bop (x, b, l, r) -> `bop (x, b, arg l, arg r)
  | `uop (x, u, a) -> `uop (x, u, arg a)
  | `sel (x, t, c, l, r) -> map_sel subst x t c l r
  | `call (x, f, args, vargs) ->
    let f = map_global subst f in
    let args = List.map args ~f:arg in
    let vargs = List.map vargs ~f:arg in
    `call (x, f, args, vargs)
  | `load (x, t, a) -> `load (x, t, arg a)
  | `store (t, v, a) -> `store (t, arg v, arg a)
  | `vastart a -> `vastart (map_global subst a)
  | `vaarg (x, t, a) -> `vaarg (x, t, map_global subst a)

let map_insn subst i =
  Insn.with_op i @@ map_op subst @@ Insn.op i

let map_tbl_entry subst i l = i, map_local subst l

let map_br subst c y n =
  let y = map_dst subst y in
  let n = map_dst subst n in
  match Map.find subst c with
  | Some `bool true -> `jmp y
  | Some `bool false -> `jmp n
  | Some `var c -> `br (c, y, n)
  | Some o -> invalid "br" o
  | None -> `br (c, y, n)

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
  | `ret None as c -> c
  | `ret (Some x) -> `ret (Some (map_arg subst x))
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
