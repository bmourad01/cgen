open Core
open Monads.Std
open Regular.Std
open Graphlib.Std
open Virtual

module O = Monad.Option

type subst = operand Var.Map.t

let match_args subst b b' =
  let open O.Let in
  let* args = match Blk.ctrl b with
    | `jmp (`label (_, args)) -> Some args
    | _ -> None in
  Blk.args b' |> Seq.to_list |> List.zip args |> function
  | Unequal_lengths -> None
  | Ok l ->
    List.fold l ~init:subst ~f:(fun subst (o, (x, _)) ->
        Map.set subst ~key:x ~data:o) |> O.return

let map_arg subst (o : operand) = match o with
  | `var x -> Map.find subst x |> Option.value ~default:o
  | _ -> o

let map_local subst : local -> local = function
  | `label (l, args) ->
    `label (l, List.map args ~f:(map_arg subst))

let map_global (subst : subst) (g : global) = match g with
  | `addr _ | `sym _ -> g
  | `var x -> match Map.find subst x with
    | Some `int (i, _) -> `addr i
    | Some (`sym _ as s) -> s
    | Some (`var _ as x) -> x
    | Some _ -> assert false
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
  | Some _ -> assert false
  | None -> `sel (x, t, c, arg l, arg r)

let map_alist (subst : subst) (a : Insn.alist) = match a with
  | `addr _ | `sym _ -> a
  | `var x -> match Map.find subst x with
    | Some (`var _ | `sym _ as a) -> a
    | Some `int (i, _) -> `addr i
    | Some _ -> assert false
    | None -> a

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
  | `alloc _ as a -> a
  | `load (x, t, a) -> `load (x, t, arg a)
  | `store (t, v, a) -> `store (t, arg v, arg a)
  | `vastart a -> `vastart (map_alist subst a)
  | `vaarg (x, t, a) -> `vaarg (x, t, map_alist subst a)

let map_insn subst i =
  Insn.create ~label:(Insn.label i) @@
  map_op subst @@ Insn.op i

let map_tbl_entry subst i l = i, map_local subst l

let map_br subst c y n =
  let y = map_dst subst y in
  let n = map_dst subst n in
  match Map.find subst c with
  | Some `bool true -> `jmp y
  | Some `bool false -> `jmp n
  | Some `var c -> `br (c, y, n)
  | Some _ -> assert false
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
    | Some _ -> assert false
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

let can_merge cfg start l l' =
  Label.(l <> l') &&
  Label.(l' <> start) &&
  not (Label.is_pseudo l') &&
  Cfg.Node.degree ~dir:`In l' cfg = 1

let try_merge tbl subst cfg start b l =
  match Seq.to_list @@ Cfg.Node.succs l cfg with
  | [l'] when can_merge cfg start l l' ->
    Hashtbl.find tbl l' |>
    Option.value_map ~default:subst ~f:(fun b' ->
        match match_args subst b b' with
        | None -> subst
        | Some subst ->
          let insns', ctrl = map_blk subst b' in
          let insns = Blk.insns b |> Seq.to_list in
          let b = Blk.create () ~ctrl ~label:l
              ~args:(Seq.to_list @@ Blk.args b)
              ~insns:(insns @ insns') in
          Hashtbl.set tbl ~key:l ~data:b;
          Hashtbl.remove tbl l';
          subst)
  | _ -> subst

let update_fn tbl fn =
  Func.blks fn |> Seq.fold ~init:fn ~f:(fun fn b ->
      let l = Blk.label b in
      if Hashtbl.mem tbl l then fn
      else Func.remove_blk_exn fn l) |>
  Func.map_blks ~f:(fun b ->
      Hashtbl.find_exn tbl @@ Blk.label b)

let rec fixpoint tbl fn =
  let cfg = Cfg.create fn in
  let start = Func.entry fn in
  let orig_len = Hashtbl.length tbl in
  let q = Stack.singleton (Label.pseudoentry, Var.Map.empty) in
  let dom = Graphlib.dominators (module Cfg) cfg Label.pseudoentry in
  while not @@ Stack.is_empty q do
    let l, subst = Stack.pop_exn q in
    Hashtbl.change tbl l ~f:(O.map ~f:(fun b ->
        if not @@ Map.is_empty subst then
          let args = Blk.args b |> Seq.to_list in
          let insns, ctrl = map_blk subst b in
          Blk.create () ~args ~insns ~ctrl ~label:l
        else b));
    let subst = match Hashtbl.find tbl l with
      | Some b -> try_merge tbl subst cfg start b l
      | None -> subst in
    Tree.children dom l |>
    Seq.iter ~f:(fun l -> Stack.push q (l, subst))
  done;
  if Hashtbl.length tbl = orig_len then fn
  else fixpoint tbl @@ update_fn tbl fn

let run fn =
  let tbl = Label.Table.create () in
  Func.blks fn |> Seq.iter ~f:(fun b ->
      Hashtbl.set tbl ~key:(Blk.label b) ~data:b);
  fixpoint tbl fn
