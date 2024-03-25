(* Merge blocks that are connected by only a single unconditional jump. *)

open Core
open Regular.Std
open Graphlib.Std
open Virtual
open Simplify_cfg_common

open O.Let

let can_merge env l l' =
  Label.(l <> l') &&
  Label.(l' <> env.start) &&
  not (Label.is_pseudo l') &&
  Cfg.Node.degree ~dir:`In l' env.cfg = 1

let candidate subst env b l =
  Cfg.Node.succs l env.cfg |> Seq.to_list |> function
  | [l'] when can_merge env l l' ->
    let* b' = Hashtbl.find env.blks l' in
    let+ subst = Subst_mapper.blk_extend subst b b' in
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
    else Subst_mapper.map_blk subst b' in
  let insns = Blk.insns b |> Seq.to_list in
  let b = Blk.create () ~ctrl ~label:l
      ~args:(Seq.to_list @@ Blk.args b)
      ~insns:(insns @ insns')
      ~dict:(Blk.dict b) in
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
  Stack.until_empty q (fun (l, subst) ->
      if not @@ Map.is_empty subst then
        Hashtbl.change env.blks l ~f:(O.map ~f:(fun b ->
            let dict = Blk.dict b in
            let args = Blk.args b |> Seq.to_list in
            let insns, ctrl = Subst_mapper.map_blk subst b in
            Blk.create () ~dict ~args ~insns ~ctrl ~label:l));
      (* If we successfully merge for the block at this label,
         then we know it has only one child in the dominator
         tree, so we can just skip forward to the child that
         we merged with. *)
      let subst, l = try_merge subst env l in
      Tree.children env.doms l |>
      Seq.iter ~f:(fun l -> Stack.push q (l, subst)));
  (* We're only ever removing blocks, so this is the only
     condition where something would've changed. *)
  Hashtbl.length env.blks < orig_len
