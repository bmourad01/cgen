(* If-conversion canonicalization.

   For the `Brsel` pass, we handle the "degenerate diamond"
   case for if-conversion, where the join block is targeted
   by both arms of the branch for our header block.

   For other cases (e.g. a proper diamond, or a triangle),
   we want to canonicalize the shape enough for other passes
   to fire, so that `Brsel` can do the final part of if-conversion.
*)

open Core
open Regular.Std
open Virtual
open Simplify_cfg_common

module BR = Simplify_cfg_brsel

type join =
  | Diamond of {
      pred1 : Label.t;
      pred2 : Label.t;
      hdr   : Label.t;
    }
  | Triangle of {
      pred : Label.t;
      hdr  : Label.t;
    }

let diamond p1 p2 h = Diamond {pred1 = p1; pred2 = p2; hdr = h}
let triangle p h = Triangle {pred = p; hdr = h}

let pp_join ppf = function
  | Diamond {pred1; pred2; hdr} ->
    Format.fprintf ppf "(diamond (hdr %a) (pred1 %a) (pred2 %a))"
      Label.pp hdr Label.pp pred1 Label.pp pred2
  | Triangle {pred; hdr} ->
    Format.fprintf ppf "(triangle (hdr %a) (pred %a))"
      Label.pp hdr Label.pp pred

exception Not_hoistable

let insn_cost : Insn.op -> int = function
  (* Provably non-trapping div/rem gets a high cost. *)
  | `bop (_, (`div #Type.imm | `rem #Type.imm), _, `int (i, _))
    when Bv.(i <> zero) -> 4
  (* Effectful or potentially trapping instructions cannot
     be hoisted. *)
  | `bop (_, (`div #Type.imm | `rem #Type.imm), _, _)
  | `load _
  | `store _
  | #Insn.variadic
  | `call _
    -> raise_notrace Not_hoistable
  (* Cheap operations. *)
  | `uop (_, #Insn.copy, _)
  | `bop (_, #Insn.arith_binop, _, _)
  | `bop (_, #Insn.bitwise_binop, _, _)
  | `bop (_, #Insn.cmp, _, _)
  | `uop (_, #Insn.arith_unop, _)
  | `uop (_, #Insn.bitwise_unop, _)
    -> 1
  (* Moderate operations. *)
  | `uop (_, #Insn.cast, _)
  | `sel _
    -> 2

let blk_cost b =
  Blk.insns b |> Seq.map ~f:Insn.op |>
  Seq.sum (module Int) ~f:insn_cost

let max_join_args = 2
let max_pred_cost = 4

let check_args tenv env fn b =
  let args = Seq.to_list @@ Blk.args b in
  List.length args <= max_join_args && try
    List.iter args ~f:(fun x ->
        ignore @@ BR.basicty tenv env fn x);
    true
  with BR.Non_basic -> false

let (.?[]) env l = Hashtbl.find env.blks l
let (.![]) env l = Hashtbl.find_exn env.blks l

let check_blk env l j = match env.?[l] with
  | None -> false
  | Some b ->
    try match Blk.ctrl b with
      | `jmp `label (l', args) when Label.(l' = j) ->
        (* Ensure that this block has no parameters.
           We have an invariant that, in its canonical
           form, the only time a block can have parameters
           is if it exists as a join point. *)
        Seq.is_empty (Blk.args b) &&
        (* Ensure correct arity *)
        Seq.length (Blk.args env.![j]) = List.length args &&
        (* Ensure that the block isn't too expensive to copy
           to the header. *)
        blk_cost b <= max_pred_cost
      | _ -> false
    with Not_hoistable -> false

let check_hdr env l s1 s2 = match env.?[l] with
  | None -> false
  | Some b -> match Blk.ctrl b with
    | `br (_, `label (l1, _), `label (l2, _)) ->
      Label.((l1 = s1 && l2 = s2) || (l1 = s2 && l2 = s1))
    | _ -> false

let plist env l = Seq.to_list @@ Cfg.Node.preds l env.cfg

let find_join tenv env fn =
  with_return @@ fun {return} ->
  Hashtbl.iteri env.blks ~f:(fun ~key ~data:b ->
      let found j = return @@ Some (key, j) in
      if check_args tenv env fn b then match plist env key with
        | [p1; p2] when Label.(p1 <> p2) ->
          begin match plist env p1, plist env p2 with
            | [p1'], _ when Label.(p1' = p2) ->
              if check_blk env p1 key
              && check_hdr env p2 p1 key
              then found @@ triangle p1 p2
            | _, [p2'] when Label.(p2' = p1) ->
              if check_blk env p2 key
              && check_hdr env p1 p2 key
              then found @@ triangle p2 p1
            | [p1'], [p2'] when Label.(p1' = p2') ->
              if check_blk env p1 key
              && check_blk env p2 key
              && check_hdr env p1' p1 p2
              then found @@ diamond p1 p2 p1'
            | _ -> ()
          end
        | _ -> ());
  None

let canonicalize_diamond env p1 p2 hdr =
  let b1 = env.![p1] and b2 = env.![p2] and h = env.![hdr] in
  let ctrl = match Blk.(ctrl h, ctrl b1, ctrl b2) with
    | `br (c, `label (l1, _), `label (l2, _)),
      `jmp (`label _ as d1),
      `jmp (`label _ as d2) ->
      if Label.(l1 = p1 && l2 = p2) then
        `br (c, d1, d2)
      else if Label.(l1 = p2 && l2 = p1) then
        `br (c, d2, d1)
      else assert false
    | _ -> assert false in
  let i1 = Seq.append (Blk.insns b1) (Blk.insns b2) in
  let h' = Blk.append_insns h @@ Seq.to_list i1 in
  let h' = Blk.with_ctrl h' ctrl in
  Hashtbl.set env.blks ~key:hdr ~data:h'

let canonicalize_triangle env key pred hdr =
  let b = env.![pred] and h = env.![hdr] in
  let ctrl = match Blk.(ctrl h, ctrl b) with
    | `br (c, `label (l1, a1), `label (l2, a2)),
      `jmp (`label _ as d) ->
      if Label.(key = l1 && pred = l2) then
        `br (c, `label (l1, a1), d)
      else if Label.(key = l2 && pred = l1) then
        `br (c, d, `label (l2, a2))
      else assert false
    | _ -> assert false in
  let h' = Blk.append_insns h @@ Seq.to_list @@ Blk.insns b in
  let h' = Blk.with_ctrl h' ctrl in
  Hashtbl.set env.blks ~key:hdr ~data:h'

let canonicalize env key = function
  | Diamond {pred1; pred2; hdr} -> canonicalize_diamond env pred1 pred2 hdr
  | Triangle {pred; hdr} -> canonicalize_triangle env key pred hdr

let run tenv env fn = match find_join tenv env fn with
  | None -> false
  | Some (key, data) ->
    canonicalize env key data;
    Logs.debug (fun m ->
        m "%s: join in $%s at %a: %a%!"
          __FUNCTION__ (Func.name fn)
          Label.pp key pp_join data);
    true
