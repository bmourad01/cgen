open Core
open Monads.Std
open Regular.Std
open Graphlib.Std
open Virtual

module O = Monad.Option

open O.Let

type subst = operand Var.Map.t

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

type env = {
  blks        : blk Label.Table.t;
  doms        : Label.t tree;
  start       : Label.t;
  mutable cfg : Cfg.t;
}

let init fn =
  let cfg = Cfg.create fn in
  let blks = Label.Table.create () in
  let doms = Graphlib.dominators (module Cfg) cfg Label.pseudoentry in
  Func.blks fn |> Seq.iter ~f:(fun b ->
      Hashtbl.set blks ~key:(Blk.label b) ~data:b);
  {blks; doms; start = Func.entry fn; cfg}

let extend subst b b' =
  let* args = match Blk.ctrl b with
    | `jmp (`label (_, args)) -> Some args
    | _ -> None in
  Blk.args b' |> Seq.to_list |> List.zip args |> function
  | Unequal_lengths -> None
  | Ok l ->
    List.fold l ~init:subst ~f:(fun subst (o, (x, _)) ->
        Map.set subst ~key:x ~data:o) |> O.return

let can_merge env l l' =
  Label.(l <> l') &&
  Label.(l' <> env.start) &&
  not (Label.is_pseudo l') &&
  Cfg.Node.degree ~dir:`In l' env.cfg = 1

let candidate subst env b l =
  Cfg.Node.succs l env.cfg |> Seq.to_list |> function
  | [l'] when can_merge env l l' ->
    let* b' = Hashtbl.find env.blks l' in
    let+ subst = extend subst b b' in
    subst, l', b'
  | _ -> None

let map_edges env l l' =
  Cfg.edges env.cfg |> Seq.filter_map ~f:(fun e ->
      let+ () = O.guard Label.(l' = Cfg.Edge.src e) in
      Cfg.Edge.(create l (dst e) (label e))) |>
  Seq.to_list

let rec try_merge ?child subst env l =
  let next () = subst, Option.value child ~default:l in
  match Hashtbl.find env.blks l with
  | None -> next ()
  | Some b -> match candidate subst env b l with
    | Some (subst, l', b') -> merge subst env l l' b b'
    | None -> next ()

and merge subst env l l' b b' =
  let insns', ctrl = if Map.is_empty subst
    then Seq.to_list (Blk.insns b'), Blk.ctrl b'
    else map_blk subst b' in
  let insns = Blk.insns b |> Seq.to_list in
  let b = Blk.create () ~ctrl ~label:l
      ~args:(Seq.to_list @@ Blk.args b)
      ~insns:(insns @ insns') in
  Hashtbl.set env.blks ~key:l ~data:b;
  Hashtbl.remove env.blks l';
  let es = map_edges env l l' in
  env.cfg <- Cfg.Node.remove l' env.cfg;
  List.iter es ~f:(fun e ->
      env.cfg <- Cfg.Edge.insert e env.cfg);
  try_merge ~child:l' subst env l

let update_fn env fn =
  Func.blks fn |> Seq.fold ~init:fn ~f:(fun fn b ->
      let l = Blk.label b in
      if Hashtbl.mem env.blks l then fn
      else Func.remove_blk_exn fn l) |>
  Func.map_blks ~f:(fun b ->
      Hashtbl.find_exn env.blks @@ Blk.label b)

let run fn =
  let env = init fn in
  let orig_len = Hashtbl.length env.blks in
  let q = Stack.singleton (Label.pseudoentry, Var.Map.empty) in
  while not @@ Stack.is_empty q do
    let l, subst = Stack.pop_exn q in
    if not @@ Map.is_empty subst then
      Hashtbl.change env.blks l ~f:(O.map ~f:(fun b ->
          let args = Blk.args b |> Seq.to_list in
          let insns, ctrl = map_blk subst b in
          Blk.create () ~args ~insns ~ctrl ~label:l));
    (* If we successfully merge for the block at this label,
       then we know it has only one child in the dominator
       tree, so we can just skip forward to the child that
       we merged with. *)
    let subst, l = try_merge subst env l in
    Tree.children env.doms l |>
    Seq.iter ~f:(fun l -> Stack.push q (l, subst))
  done;
  (* We're only ever removing blocks, so this is the only
     condition where something would've changed. *)
  if Hashtbl.length env.blks < orig_len
  then update_fn env fn else fn
