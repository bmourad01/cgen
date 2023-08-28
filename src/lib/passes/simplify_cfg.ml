open Core
open Monads.Std
open Regular.Std
open Graphlib.Std
open Virtual

module O = Monad.Option
module E = Monad.Result.Error

open O.Let
open O.Syntax

(* Helpers for substituting block arguments. *)

type subst = operand Var.Map.t

let invalid ctx o =
  let s = Format.asprintf "%a" pp_operand o in
  failwithf "Invalid %s operand %s" ctx s ()

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

let map_alist (subst : subst) (a : Insn.alist) = match a with
  | `addr _ | `sym _ -> a
  | `var x -> match Map.find subst x with
    | Some (`var _ | `sym _ as a) -> a
    | Some `int (i, _) -> `addr i
    | Some o -> invalid "alist" o
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

let extend subst b b' =
  let* args = match Blk.ctrl b with
    | `jmp (`label (_, args)) ->
      !!(List.map args ~f:(map_arg subst))
    | _ -> None in
  Blk.args b' |> Seq.to_list |> List.zip args |> function
  | Unequal_lengths -> None
  | Ok l ->
    List.fold l ~init:subst ~f:(fun subst (o, x) ->
        Map.set subst ~key:x ~data:o) |> O.return

(* Various state. *)

type env = {
  blks        : blk Label.Table.t;
  doms        : Label.t tree;
  start       : Label.t;
  mutable cfg : Cfg.t;
}

let init fn =
  let cfg = Cfg.create fn in
  let start = Func.entry fn in
  let blks = Label.Table.create () in
  let doms = Graphlib.dominators (module Cfg) cfg Label.pseudoentry in
  Func.blks fn |> Seq.iter ~f:(fun b ->
      Hashtbl.set blks ~key:(Blk.label b) ~data:b);
  {blks; doms; start; cfg}

let update_fn env fn =
  Func.blks fn |> Seq.fold ~init:fn ~f:(fun fn b ->
      let l = Blk.label b in
      if Hashtbl.mem env.blks l then fn
      else Func.remove_blk_exn fn l) |>
  Func.map_blks ~f:(fun b ->
      Hashtbl.find_exn env.blks @@ Blk.label b)

let not_pseudo = Fn.non Label.is_pseudo

let is_disjoint env l =
  not_pseudo l &&
  Label.(l <> env.start) &&
  Cfg.Node.preds l env.cfg |>
  Seq.filter ~f:not_pseudo |>
  Seq.is_empty

let recompute_cfg env fn =
  env.cfg <- Cfg.create fn;
  Cfg.nodes env.cfg |> Seq.fold ~init:fn ~f:(fun fn l ->
      if is_disjoint env l then begin
        (* This block has no more references, so we can
           safely delete it. *)
        env.cfg <- Cfg.Node.remove l env.cfg;
        Hashtbl.remove env.blks l;
        Func.remove_blk_exn fn l
      end else fn)

(* Merge blocks that are connected by only a single unconditional jump. *)

module Merge = struct
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

  let run env =
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
    Hashtbl.length env.blks < orig_len
end

(* Contract edges in the CFG when we find blocks with no instructions
   and a single unconditional jump. *)

module Contract = struct
  type singles = dst Label.Tree.t

  type chain =
    | Dest of dst
    | Next of Label.t * Label.t * chain

  let can_be_single env l b =
    Label.(l <> env.start) &&
    Seq.is_empty (Blk.insns b)

  let singles env : singles =
    Hashtbl.fold env.blks ~init:Label.Tree.empty
      ~f:(fun ~key:l ~data:b m -> match Blk.ctrl b with
          | `jmp d when can_be_single env l b ->
            Label.Tree.set m ~key:l ~data:d
          | _ -> m)

  (* Chase down the final destination. *)
  let chase ?(local_only = false) (s : singles) l =
    let rec aux l vis =
      let* () = O.guard @@ not @@ Set.mem vis l in
      Label.Tree.find s l >>= function
      | #global when local_only -> None
      | #global as g -> !!(Dest g)
      | `label (l', _) as loc ->
        match aux l' @@ Set.add vis l with
        | Some x -> !!(Next (l, l', x))
        | None -> !!(Dest loc) in
    aux l Label.Set.empty

  (* Perform the substitutions on block arguments for the entire chain. *)
  let rec eval subst env = function
    | Dest d -> !!(map_dst subst d)
    | Next (l, l', x) ->
      let* b = Hashtbl.find env.blks l in
      let* b' = Hashtbl.find env.blks l' in
      let* subst = extend subst b b' in
      eval subst env x

  let init_subst env l args =
    let* b = Hashtbl.find env.blks l in
    let args' = Seq.to_list @@ Blk.args b in
    match List.zip args' args with
    | Unequal_lengths -> None
    | Ok xs -> match Var.Map.of_alist xs with
      | `Ok m -> !!m
      | `Duplicate_key x ->
        (* This shouldn't happen if we passed the type checker. *)
        failwithf "Couldn't create substitution for block %a: \
                   duplicate var %a" Label.pps l Var.pps x ()

  let find_dst env s : dst -> dst option = function
    | #global -> None
    | `label (l, args) ->
      let* subst = init_subst env l args in
      chase s l >>= eval subst env

  let find_loc env s : local -> local option = function
    | `label (l, args) ->
      let* subst = init_subst env l args in
      chase s l ~local_only:true >>=
      eval subst env >>| function
      | #global -> assert false
      | #local as l -> l

  let map_dst changed env s d = match find_dst env s d with
    | Some x -> changed := true; x
    | None -> d

  let map_loc changed env s l = match find_loc env s l with
    | Some x -> changed := true; x
    | None -> l

  let sw_all_same d tbl =
    Ctrl.Table.enum tbl |> Seq.map ~f:snd |>
    Seq.fold_until ~init:d ~finish:(fun _ -> true)
      ~f:(fun l l' -> if equal_local l l'
           then Continue l' else Stop false)

  let contract_blk changed env (s : singles) b =
    let dst = map_dst changed env s in
    let loc = map_loc changed env s in
    Blk.map_ctrl b ~f:(function
        | `hlt | `ret _ as x -> x
        | `jmp d -> `jmp (dst d)
        | `br (c, y, n) ->
          let y = dst y in
          let n = dst n in
          if equal_dst y n then `jmp y else `br (c, y, n)
        | `sw (t, i, d, tbl) ->
          let d = loc d in
          let tbl = Ctrl.Table.map_exn tbl ~f:(fun i l -> i, loc l) in
          if sw_all_same d tbl
          then `jmp (d :> dst)
          else `sw (t, i, d, tbl))

  let run env =
    let changed = ref false in
    Hashtbl.map_inplace env.blks
      ~f:(contract_blk changed env @@ singles env);
    !changed
end

let try_ f = try Ok (f ()) with
  | Failure msg ->
    Monad.Result.Error.failf "In simplify_cfg: %s" msg ()

let run fn =
  if Dict.mem (Func.dict fn) Tags.ssa then
    let env = init fn in
    let upd = update_fn env in
    let rec loop fn =
      let merged = Merge.run env in
      if Contract.run env then loop @@ recompute_cfg env @@ upd fn
      else if merged then upd fn
      else fn in
    try_ @@ fun () -> loop fn
  else E.failf "Expected SSA form for function %s"
      (Func.name fn) ()
