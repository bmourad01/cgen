open Core
open Pseudo
open X86_amd64_common.Insn

module Rv = X86_amd64_common.Regvar
module Ltree = Label.Tree
module Lset = Label.Tree_set
module LS = Label.Dense_set
module P = Pseudo_passes.Peephole

let decomp i = Insn.label i, Insn.insn i

let rbp_ = Rv.reg `rbp

let albl_of_op = function
  | Omem (Albl (l, _), _) -> Some l
  | _ -> None

let albl_of_insn = function
  | Two (_, a, b) -> List.filter_map [a; b] ~f:albl_of_op
  | One (_, a) -> Option.to_list (albl_of_op a)
  | JMP (Jind a) -> Option.to_list (albl_of_op a)
  | _ -> []

let reg_is_index r = function
  | Omem (Abis (_, i, _), _)
  | Omem (Aisd (i, _, _), _)
  | Omem (Abisd (_, i, _, _), _) -> Rv.(i = r)
  | _ -> false

let operand_is_reg r = function
  | Oreg (a, _)
  | Oregv a -> Rv.(a = r)
  | _ -> false

(* Combine two displacements, being careful to check that the result will
   fit in a sign-extended 32-bit immediate. *)
let combine_disp disp o =
  let s = Int64.(of_int32 disp + of_int32 o) in
  Option.some_if
    Int64.(
      s >= of_int32 Int32.min_value &&
      s <= of_int32 Int32.max_value)
    (Int64.to_int32_trunc s)

let fold_base r disp = function
  | Omem (a, t) ->
    let fp = Rv.reg `rbp in
    let a = match a with
      | Ab b when Rv.(b = r) -> Some (Abd (fp, disp))
      | Abd (b, o) when Rv.(b = r) ->
        Option.map (combine_disp disp o) ~f:(fun d -> Abd (fp, d))
      | Abis (b, i, s) when Rv.(b = r) -> Some (Abisd (fp, i, s, disp))
      | Abisd (b, i, s, o) when Rv.(b = r) ->
        Option.map (combine_disp disp o) ~f:(fun d -> Abisd (fp, i, s, d))
      | a -> Some a in
    Option.map a ~f:(fun a -> Omem (a, t))
  | o -> Some o

let and_test_cc = function
  | Ce | Cne | Cs | Cns -> true
  | _ -> false

let and_test_act = function
  | Jcc (cc, _)
  | One (SETcc cc, _)
  | Two (CMOVcc cc, _, _)
    -> and_test_cc cc
  | _ -> false

(* TODO: fill me in *)
let combinable_binop = function
  | ADD
  | SUB
  | IMUL2
  | AND
  | OR
  | XOR
  | TEST_
  | CMP -> true
  | _ -> false

(* Combine with unary ops that don't write to their operand. *)
let combinable_unop = function
  | CALL _
  | DIV
  | IDIV
  | IMUL1
  | MUL -> true
  | _ -> false

let immty = function
  | #Type.imm as imm -> imm
  | _ -> assert false

(* True if `o` can be directly encoded as an immediate operand for a
   combinable binop applied to an `r1t`-typed destination.

   In 64-bit mode, binary instructions (ADD, SUB, CMP, TEST, AND, OR,
   XOR, IMUL2) only support sign-extended imm32 immediates. A 64-bit
   immediate that doesn't fit in that range must stay in a register.
*)
let combinable_imm r1t = function
  | Oimm (i, `i64) when Type.equal_basic r1t `i64 ->
    Int64.(i >= -0x80000000L && i <= 0x7FFFFFFFL)
  | _ -> true

let rset_mem' o l =
  let s = rset o in
  List.exists l ~f:(Set.mem s)

let map_insns changed fn t =
  if Ltree.is_empty t then fn else
    let () = changed := true in
    Func.map_blks fn ~f:(fun b ->
        Blk.map_insns b ~f:(fun i ->
            match Ltree.find t @@ Insn.label i with
            | Some insn -> Insn.with_insn i insn
            | None -> i))

let filter_not_in changed fn t =
  if Lset.is_empty t then fn else
    let () = changed := true in
    Func.map_blks fn ~f:(fun b ->
        Blk.filter_insns b ~f:(fun i ->
            not @@ Lset.mem t @@ Insn.label i))

let take_seq_singleton s =
  Sequence.take s 2 |> Sequence.to_list |> function
  | [x] -> Some x
  | _ -> None

(* Blocks that consist of a single instruction of the form:

   @label:
     jmp @otherlabel
*)
let collect_singles fn =
  let start = Func.start fn in
  Func.fold_blks fn ~init:Ltree.empty ~f:(fun acc b ->
      let key = Blk.label b in
      if Label.(key = start) then acc else
        Blk.insns b |> Sequence.map ~f:Insn.insn |>
        take_seq_singleton |> function
        | Some JMP Jlbl dst -> Ltree.set acc ~key ~data:dst
        | _ -> acc)

(* Union-find with path compression. *)
let find_with_compression changed m l =
  let parent l = Ltree.find !m l |> Option.value ~default:l in
  let l = ref l and orig = l in
  let p = ref @@ parent orig in
  while Label.(!l <> !p) do
    let g = parent !p in
    if Label.(g <> !p) then begin
      m := Ltree.set !m ~key:!l ~data:g;
      p := parent g
    end;
    l := g
  done;
  if Label.(!p <> orig) then changed := true;
  !p

(* For blocks collected in the above analysis, thread them through to
   the final destination.

   Example:

   @1:
     ...
     jmp @2
   @2:
     jmp @3
   @3:
     ...

   becomes

   @1:
     ...
     jmp @3
   @2:        <--- if nobody references this block anymore, it can be removed
     jmp @3
   @3:
     ...
*)
let jump_threading changed fn =
  let singles = collect_singles fn in
  if not @@ Label.Tree.is_empty singles then
    let find = find_with_compression changed @@ ref singles in
    Func.map_blks fn ~f:(fun b ->
        Blk.map_insns b ~f:(fun i ->
            Insn.with_insn i @@ match Insn.insn i with
            | Jcc (cc, dst) -> Jcc (cc, find dst)
            | JMP (Jlbl dst) -> JMP (Jlbl (find dst))
            | JMPtbl (d, ls) -> JMPtbl (find d, List.map ls ~f:find)
            | insn -> insn))
  else fn

let not_pseudo i = not @@ is_pseudo @@ Insn.insn i
let has_dests i = not @@ Lset.is_empty @@ dests @@ Insn.insn i

let is_merge_candidate cfg b1 b2 =
  match Blk.insns b1 ~rev:true |> Sequence.find ~f:not_pseudo with
  (* `b1` must fall through into `b2`, unconditionally. *)
  | Some i when is_barrier (Insn.insn i) || has_dests i -> false
  | Some _ | None ->
    let l1 = Blk.label b1 and l2 = Blk.label b2 in Sequence.(
      equal Label.equal (Cfg.Node.succs l1 cfg) (singleton l2) &&
      equal Label.equal (Cfg.Node.preds l2 cfg) (singleton l1))

(* find m l = None ==> no change
   find m l = Some None ==> delete
   find m l = Some (Some b) ==> replace *)
let collect_merge_blks fn =
  let cfg = Cfg.create ~is_barrier ~is_pseudo ~dests fn in
  let rec go m = function
    | [] | [_] -> m
    | b1 :: b2 :: rest when is_merge_candidate cfg b1 b2 ->
      let label = Blk.label b1 in
      let insns =
        Blk.insns ~rev:true b1 |> Sequence.fold
          ~init:(Sequence.to_list @@ Blk.insns b2)
          ~f:(fun acc i -> i :: acc) in
      let b1' = Blk.create ~label ~insns in
      let m = Ltree.add_exn m ~key:label ~data:(Some b1') in
      let m = Ltree.add_exn m ~key:(Blk.label b2) ~data:None in
      go m rest
    | _ :: rest -> go m rest in
  Func.blks fn |> Sequence.to_list |> go Ltree.empty

let merge_blks changed fn =
  let m = collect_merge_blks fn in
  if Ltree.is_empty m then fn else
    let () = changed := true in
    Func.filter_map_blks fn ~f:(fun b ->
        match Ltree.find m @@ Blk.label b with
        | None -> Some b | Some b' -> b')

(* Remove blocks that are not reachable from the entry block. *)
let remove_disjoint changed fn =
  let reachable =
    let cfg = Cfg.create ~is_barrier ~is_pseudo ~dests fn in
    let start = Func.entry fn in
    let vis = LS.create ~capacity:(Cfg.number_of_nodes cfg) () in
    let q = Stack.singleton start in
    Stack.until_empty q (fun n ->
        if LS.strict_add vis n then
          Cfg.Node.succs n cfg |> Sequence.iter ~f:(Stack.push q));
    vis in
  let dead =
    Func.blks fn |> Sequence.map ~f:Blk.label |>
    Sequence.filter ~f:(Fn.non @@ LS.mem reachable) |>
    Sequence.to_list in
  if not @@ List.is_empty dead then changed := true;
  Func.remove_blks_exn fn dead

(* Invert conditional branches based on the block layout.

   Example:

   @1:
     ...
     jne @2
     jmp @3
   @2:
     ...
   @3:
     ...

   becomes

   @1:
     ...
     je @3
     jmp @2  <--- this jump can now be turned into a fallthrough later
   @2:
     ...
   @3:
     ...
*)
let collect_invert_branches afters fn =
  Func.fold_blks fn ~init:Ltree.empty ~f:(fun acc b ->
      Blk.label b |> Ltree.find afters |>
      Option.value_map ~default:acc ~f:(fun after ->
          Blk.insns b ~rev:true |> Sequence.map ~f:decomp |>
          Fn.flip Sequence.take 2 |> Sequence.to_list |> function
          | [lb, JMP (Jlbl b); la, Jcc (cc, a)] when Label.(a = after) ->
            Ltree.set
              (Ltree.set acc ~key:la ~data:(Jcc (negate_cc cc, b)))
              ~key:lb ~data:(JMP (Jlbl a))
          | _ -> acc))

let invert_branches changed afters fn =
  map_insns changed fn @@ collect_invert_branches afters fn

(* Eliminate useless unconditional jumps where a fallthrough would suffice.

   Example:

   @1:
     ...
     jmp @2
   @2:
     ...

   becomes

   @1:
     ...
   @2:     <--- block @1 implicitly falls through to block @2
     ...
*)
let collect_implicit_fallthroughs afters fn =
  Func.fold_blks fn ~init:Lset.empty ~f:(fun acc b ->
      Blk.label b |> Ltree.find afters |>
      Option.value_map ~default:acc ~f:(fun after ->
          Blk.insns b ~rev:true |>
          Sequence.map ~f:decomp |> Sequence.hd |> function
          | Some (la, JMP (Jlbl a)) when Label.(a = after) ->
            Lset.add acc la
          | _ -> acc))

let implicit_fallthroughs changed afters fn =
  filter_not_in changed fn @@ collect_implicit_fallthroughs afters fn

module Window_rules = struct
  module V = P.View
  module Rule_syntax = P.Rule_syntax
  open P.Edit
  open P.Take

  (* Deallocating the stack pointer followed by a LEAVE instruction
     is redundant.

     Example:

     @1:
       ...
       call $foo         <--- $foo takes arguments on the stack
       add rsp, 0x10_l   <--- space for stack args is cleaned up
       leave             <--- restore stack pointer and return
       ret

     becomes

     @1:
       call $foo
       leave
       ret

     because LEAVE will overwrite RSP anyway
  *)
  let r_dealloc_stack_before_leave = [%rule fun p i ->
    let T2 (Two (ADD, Oreg (r, `i64), Oimm _), LEAVE) = V.take p i K2 in
    guard (Rv.has_reg r `rsp);
    [Delete i], i + 2
  ]

  let r_redundant_spill_after_reload = [%rule fun p i ->
    let T2 (Two (MOV, Oreg (r2, _), Omem (a2, t2)),
            Two (MOV, Omem (a1, t1), Oreg (r1, _))) = V.take p i K2 in
    guard (equal_amode a1 a2 && equal_memty t1 t2 && Rv.(r1 = r2));
    [Delete (i + 1)], i + 2
  ]

  (* Dual of the above: eliminate a reload immediately after a store
     to the same slot.

       mov [mem], r     ; store
       mov r', [mem]    ; reload (redundant)

     If r = r', the reload is dead and removed.
     If r <> r', rewrite to: mov r', r
  *)
  let r_redundant_reload_after_spill = [%rule fun p i ->
    let T2 (Two (MOV, Omem (a1, t1), Oreg (r1, r1t)),
            Two (MOV, Oreg (r2, r2t), Omem (a2, t2))) = V.take p i K2 in
    guard (equal_amode a1 a2 && equal_memty t1 t2 && Type.equal_basic r1t r2t);
    if Rv.(r1 = r2) then
      [Delete (i + 1)], i + 2
    else
      let ins = Two (MOV, Oreg (r2, r2t), Oreg (r1, r1t)) in
      [Rewrite (i + 1, ins)], i + 2
  ]

  (* Fold a frame-relative address materialized by a LEA into the MOV memory
     operands that consume it as a base, dropping the LEA.

       lea r, [rbp + k]
       mov d, [r + o]    --> mov d, [rbp + k + o]
       mov r, [r + o']   --> mov r, [rbp + k + o']   ; the LEA is dropped
  *)
  let r_fold_frame_lea = [%rule fun p i ->
    let T1 Two (LEA, Oreg (r, _), addr) = V.take p i K1 in
    let Omem ((Ab bb | Abd (bb, _)) as am, _) = addr in
    guard Rv.(bb = rbp_ && r <> rbp_);
    let disp = match am with Abd (_, d) -> d | _ -> 0l in
    let rec scan = [%rule fun j folds ->
      let T1 Two (MOV, dst, src) = V.take p j K1 in
      let ops = [dst; src] in
      (* r not touched here: keep walking. *)
      if not (Set.mem (rset ops) r)
      then continue (scan (j + 1) folds)
      else begin
        (* r must not be used as an index, nor be the source. *)
        guard (not (List.exists ops ~f:(reg_is_index r)));
        guard (not (operand_is_reg r src));
        let Some dst = fold_base r disp dst in
        let Some src = fold_base r disp src in
        let folds = (j, Two (MOV, dst, src)) :: folds in
        (* r written here: this is the last fold. *)
        if operand_is_reg r dst then folds
        else continue (scan (j + 1) folds)
      end
    ] in
    match scan (i + 1) [] with
    | None | Some [] -> fail
    | Some folds ->
      let edits =
        Delete i ::
        List.map folds ~f:(fun (j, ins) ->
            Rewrite (j, ins)) in
      edits, i + 1
  ]

  (* If we have a LEA of the same address as a subsequent load,
     then use the result of the LEA as the address for the load.

     This is made under the assumption that the result of the LEA
     is going to be re-used later (otherwise it would have been
     recognized as dead code).
  *)
  let r_reuse_lea = [%rule fun p i ->
    let T2 (Two (LEA, Oreg (r1, _), Omem (a1, _)),
            Two (MOV, Oreg (r2, r2t), Omem (a2, t2))) = V.take p i K2 in
    guard (equal_amode a1 a2);
    let ins = Two (MOV, Oreg (r2, r2t), Omem (Ab r1, t2)) in
    [Rewrite (i + 1, ins)], i + 2
  ]

  (* If we have an AND followed by a TEST/CMP, then we can possibly
     delete the latter, since AND sets RFLAGS and could carry the
     desired test. *)
  let r_and_test = [%rule fun p i ->
    let T3 (Two (AND, Oreg (r1, _), _), b, act) = V.take p i K3 in
    guard (and_test_act act);
    match b with
    | Two (TEST_, Oreg (r1', _), Oreg (r2', _))
      when Rv.(r1 = r1' && r1 = r2') -> [Delete (i + 1)], i + 3
    | Two (CMP, Oreg (r1', _), Oimm (0L, _))
      when Rv.(r1 = r1') -> [Delete (i + 1)], i + 3
    | _ -> fail
  ]

  (* Fuses:

       lea r1, [b + d]
       mov b, r1

     into:

       add b, d
  *)
  let r_lea_mov = [%rule fun p i ->
    let T2 (Two (LEA, Oreg (r1, _), Omem (Abd (b, d), _)),
            Two (MOV, Oreg (r1', r1t), Oreg (r2', _))) = V.take p i K2 in
    guard (Rv.(b = r1') && Rv.(r1 = r2'));
    let ins = match d with
      | 1l -> One (INC, Oreg (r1', r1t))
      | _ ->
        let d = Int64.(of_int32 d land 0xFFFFFFFFL) in
        Two (ADD, Oreg (r1', r1t), Oimm (d, immty r1t)) in
    [Rewrite (i + 1, ins)], i + 2]

  (* Fuses a just-loaded operand directly into the op that consumes it, e.g.:

       mov r1, o
       op r2, r1

     into:

       op r2, o
  *)
  let r_mov_binop_3 = [%rule fun p i ->
    let T3 (Two (MOV, Oreg (r1, mt), o1),
            Two (MOV, Oreg (r2, _), o2),
            Two (op, Oreg (r3, r3t), Oreg (r3', _))) = V.take p i K3 in
    guard (combinable_binop op
           && Rv.(r1 = r3')
           && Rv.(r2 = r3)
           && Rv.(r3 <> r3')
           && Type.equal_basic mt r3t
           && not (rset_mem' [o1; o2] [r1; r3])
           && combinable_imm r3t o1);
    let ins = Two (op, Oreg (r3, r3t), o1) in
    [Rewrite (i + 2, ins)], i + 3
  ]

  (* Same as above, but for a two-instruction window. *)
  let r_mov_binop_2 = [%rule fun p i ->
    let T2 (Two (MOV, Oreg (r1, mt), o), b) = V.take p i K2 in
    guard (not (Set.mem (rset [o]) r1));
    let Two (op, Oreg (r1', r1t), Oreg (r2', _)) = b in
    guard (combinable_binop op
           && Rv.(r1 = r2')
           && Rv.(r1' <> r2')
           && Type.equal_basic mt r1t
           && combinable_imm r1t o);
    [Rewrite (i + 1, Two (op, Oreg (r1', r1t), o))], i + 2
  ]

  (* Same as above, but for a unary operator. *)
  let r_mov_unop_2 = [%rule fun p i ->
    let T2 (Two (MOV, Oreg (r1, mt), o), b) = V.take p i K2 in
    guard (not (Set.mem (rset [o]) r1));
    let One (op, Oreg (r2', ut)) = b in
    guard (combinable_unop op
           && Rv.(r1 = r2')
           && Type.equal_basic mt ut);
    [Rewrite (i + 1, One (op, o))], i + 2
  ]

  (* Fuses:

       mov r1, r2
       mov [o], r1

     into:

       mov [o], r2
  *)
  let r_mov_to_store = [%rule fun p i ->
    let T2 (Two (MOV, Oreg (r1, r1t), (Oreg _ as r)),
            Two (MOV, (Omem _ as o), Oreg (r2, r2t))) = V.take p i K2 in
    guard (Rv.(r1 = r2) && Type.equal_basic r1t r2t);
    [Rewrite (i + 1, Two (MOV, o, r))], i + 2
  ]

  let prio = [
    r_dealloc_stack_before_leave;
    r_redundant_spill_after_reload;
    r_redundant_reload_after_spill;
    r_reuse_lea;
    r_fold_frame_lea;
    r_and_test;
    r_lea_mov;
    r_mov_binop_3;
    r_mov_binop_2;
    r_mov_unop_2;
    r_mov_to_store;
  ]
end

let collect_dead_fp_pseudos fn =
  let refs =
    Func.fold_blks fn ~init:Lset.empty ~f:(fun acc b ->
        Blk.insns b |> Sequence.map ~f:Insn.insn |>
        Sequence.fold ~init:acc ~f:(fun acc -> function
            | FP32 _ | FP64 _ | FP32V _ | FP64V _ -> acc
            | i -> albl_of_insn i |> List.fold ~init:acc ~f:Lset.add)) in
  Func.fold_blks fn ~init:Lset.empty ~f:(fun acc b ->
      Blk.fold_insns b ~init:acc ~f:(fun acc i ->
          match Insn.insn i with
          | FP32 (l, _) | FP64 (l, _) | FP32V (l, _) | FP64V (l, _)
            when not (Lset.mem refs l) -> Lset.add acc (Insn.label i)
          | _ -> acc))

let remove_dead_fp_pseudos changed fn =
  filter_not_in changed fn @@ collect_dead_fp_pseudos fn

let max_rounds = 5

let run fn =
  let rec loop i fn =
    if i > max_rounds then fn else
      let () = Logs.debug (fun m ->
          m "%s: peephole round %d%!" __FUNCTION__ i) in
      let changed = ref false in
      let fn = jump_threading changed fn in
      let fn = remove_disjoint changed fn in
      let fn = merge_blks changed fn in
      let afters = Func.collect_afters fn in
      let fn = invert_branches changed afters fn in
      let fn = implicit_fallthroughs changed afters fn in
      let fn = Pseudo_passes.Peephole.run ~changed ~rules:Window_rules.prio fn in
      let fn = remove_dead_fp_pseudos changed fn in
      if !changed then loop (i + 1) fn else fn in
  loop 1 fn
