open Core
open Regular.Std
open Graphlib.Std
open Pseudo
open X86_amd64_common.Insn

module Rv = X86_amd64_common.Regvar
module Ltree = Label.Tree
module Lset = Label.Tree_set

let decomp i = Insn.label i, Insn.insn i

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
        Blk.insns b |> Seq.filter ~f:(fun i ->
            not @@ Lset.mem t @@ Insn.label i) |>
        Seq.to_list |> Blk.with_insns b)

(* Blocks that consist of a single instruction of the form:

   @label:
     jmp @otherlabel
*)
let collect_singles fn =
  let start = Func.start fn in
  Func.fold_blks fn ~init:Ltree.empty ~f:(fun acc b ->
      let key = Blk.label b in
      if Label.(key = start) then acc else
        let is = Seq.map ~f:Insn.insn @@ Blk.insns b in
        match Seq.next is with
        | Some (JMP (Jlbl dst), rest) when Seq.is_empty rest ->
          Ltree.set acc ~key ~data:dst
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

let is_merge_candidate cfg b1 b2 =
  match Blk.insns b1 ~rev:true |> Seq.find ~f:not_pseudo with
  | Some i when is_barrier (Insn.insn i) -> false
  | Some _ | None ->
    let l1 = Blk.label b1 and l2 = Blk.label b2 in Seq.(
      equal Label.equal (Cfg.Node.succs l1 cfg) (singleton l2) &&
      equal Label.equal (Cfg.Node.preds l2 cfg) (singleton l1))

(* find m l = None ==> no change
   find m l = Some None ==> delete
   find m l = Some (Some b) ==> replace *)
let collect_merge_blks fn =
  let cfg = Cfg.create ~is_barrier ~is_pseudo ~dests fn in
  let rec go m = function
    | [] | [_] -> m
    | b1 :: b2 :: rest  when is_merge_candidate cfg b1 b2 ->
      let label = Blk.label b1 in
      let insns = Seq.(to_list @@ append (Blk.insns b1) (Blk.insns b2)) in
      let b1' = Blk.create ~label ~insns in
      let m = Ltree.add_exn m ~key:label ~data:(Some b1') in
      let m = Ltree.add_exn m ~key:(Blk.label b2) ~data:None in
      go m rest
    | _ :: rest -> go m rest in
  Func.blks fn |> Seq.to_list |> go Ltree.empty

let merge_blks changed fn =
  let m = collect_merge_blks fn in
  if Ltree.is_empty m then fn else
    let () = changed := true in
    Func.blks fn |> Seq.filter_map ~f:(fun b ->
        match Ltree.find m @@ Blk.label b with
        | None -> Some b | Some b' -> b') |>
    Seq.to_list |> Func.with_blks fn

(* Remove blocks that are not reachable from the entry block. *)
let remove_disjoint changed fn =
  let reachable = with_return @@ fun {return} ->
    let cfg = Cfg.create ~is_barrier ~is_pseudo ~dests fn in
    let start = Func.entry fn in
    Graphlib.depth_first_search (module Cfg) cfg ~start
      ~init:Lset.empty
      ~start_tree:(fun n s ->
          if Label.(n = start) then s else return s)
      ~enter_node:(fun _ n s -> Lset.add s n) in
  let dead =
    Func.blks fn |> Seq.map ~f:Blk.label |>
    Seq.filter ~f:(Fn.non @@ Lset.mem reachable) |>
    Seq.to_list in
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
          Blk.insns b ~rev:true |> Seq.map ~f:decomp |>
          Fn.flip Seq.take 2 |> Seq.to_list |> function
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
          Seq.map ~f:decomp |> Seq.hd |> function
          | Some (la, JMP (Jlbl a)) when Label.(a = after) ->
            Lset.add acc la
          | _ -> acc))

let implicit_fallthroughs changed afters fn =
  filter_not_in changed fn @@ collect_implicit_fallthroughs afters fn

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
let collect_dealloc_stack_before_leave fn =
  Func.fold_blks fn ~init:Lset.empty ~f:(fun acc b ->
      let rec go acc = function
        | [] | [_] -> acc
        | (l, Two (ADD, Oreg (r, `i64), Oimm _))
          :: (_, LEAVE)
          :: xs when Rv.has_reg r `rsp ->
          let acc = Lset.add acc l in
          go acc xs
        | _ :: xs -> go acc xs in
      go acc @@ Seq.to_list @@ Seq.map ~f:decomp @@ Blk.insns b)

let dealloc_stack_before_leave changed fn =
  filter_not_in changed fn @@ collect_dealloc_stack_before_leave fn

let collect_redundant_spill_after_reload fn =
  Func.fold_blks fn ~init:Lset.empty ~f:(fun acc b ->
      let rec go acc = function
        | [] | [_] -> acc
        | (_, Two (MOV, Oreg (r2, _), Omem (a2, t2)))
          :: (l, Two (MOV, Omem (a1, t1), Oreg (r1, _)))
          :: xs when equal_amode a1 a2
                  && equal_memty t1 t2
                  && Rv.(r1 = r2) ->
          let acc = Lset.add acc l in
          go acc xs
        | _ :: xs -> go acc xs in
      go acc @@ Seq.to_list @@ Seq.map ~f:decomp @@ Blk.insns b)

let redundant_spill_after_reload changed fn =
  filter_not_in changed fn @@ collect_redundant_spill_after_reload fn

(* Dual of the above: eliminate a reload immediately after a store
   to the same slot.

     mov [mem], r     ; store
     mov r', [mem]    ; reload (redundant)

   If r = r', the reload is dead and removed.
   If r <> r', rewrite to: mov r', r
*)
let collect_redundant_reload_after_spill fn =
  Func.fold_blks fn
    ~init:(Ltree.empty, Lset.empty)
    ~f:(fun acc b ->
        let rec go ((rw, rm) as acc) = function
          | [] | [_] -> acc
          | (_, Two (MOV, Omem (a1, t1), Oreg (r1, r1t)))
            :: (l, Two (MOV, Oreg (r2, r2t), Omem (a2, t2)))
            :: xs when equal_amode a1 a2
                    && equal_memty t1 t2
                    && Type.equal_basic r1t r2t ->
            if Rv.(r1 = r2) then
              go (rw, Lset.add rm l) xs
            else
              let data = Two (MOV, Oreg (r2, r2t), Oreg (r1, r1t)) in
              go (Ltree.set rw ~key:l ~data, rm) xs
          | _ :: xs -> go acc xs in
        go acc @@ Seq.to_list @@ Seq.map ~f:decomp @@ Blk.insns b)

let redundant_reload_after_spill changed fn =
  let rw, rm = collect_redundant_reload_after_spill fn in
  filter_not_in changed (map_insns changed fn rw) rm

(* If we have a LEA of the same address as a subsequent load,
   then use the result of the LEA as the address for the load.

   This is made under the assumption that the result of the LEA
   is going to be re-used later (otherwise it would have been
   recognized as dead code).
*)
let collect_reuse_lea fn =
  Func.fold_blks fn ~init:Ltree.empty ~f:(fun acc b ->
      let rec go acc = function
        | [] | [_] -> acc
        | (_, Two (LEA, Oreg (r1, _), Omem (a1, _)))
          :: (l, Two (MOV, Oreg (r2, r2t), Omem (a2, t2)))
          :: xs when equal_amode a1 a2 ->
          let data = Two (MOV, Oreg (r2, r2t), Omem (Ab r1, t2)) in
          let acc = Ltree.set acc ~key:l ~data in
          go acc xs
        | _ :: xs -> go acc xs in
      go acc @@ Seq.to_list @@ Seq.map ~f:decomp @@ Blk.insns b)

let reuse_lea changed fn =
  map_insns changed fn @@ collect_reuse_lea fn

let and_test_cc = function
  | Ce | Cne | Cs | Cns -> true
  | _ -> false

let and_test_act = function
  | Jcc (cc, _)
  | One (SETcc cc, _)
  | Two (CMOVcc cc, _, _)
    -> and_test_cc cc
  | _ -> false

let collect_and_test fn =
  Func.fold_blks fn ~init:Lset.empty ~f:(fun acc b ->
      let rec go acc = function
        | [] | [_] -> acc
        | (_, Two (AND, Oreg (r1, _), _))
          :: (l, Two (TEST_, Oreg (r1', _), Oreg (r2', _)))
          :: (_, act)
          :: xs when Rv.(r1 = r1')
                  && Rv.(r1 = r2')
                  && and_test_act act ->
          go (Lset.add acc l) xs
        | (_, Two (AND, Oreg (r1, _), _))
          :: (l, Two (CMP, Oreg (r1', _), Oimm (0L, _)))
          :: (_, act)
          :: xs when Rv.equal r1 r1'
                  && and_test_act act ->
          go (Lset.add acc l) xs
        | _ :: xs -> go acc xs in
      go acc @@ Seq.to_list @@ Seq.map ~f:decomp @@ Blk.insns b)

let and_test changed fn =
  filter_not_in changed fn @@ collect_and_test fn

let immty = function
  | #Type.imm as imm -> imm
  | _ -> assert false

(* True if `o` can be directly encoded as an immediate operand for a
   combinable binop applied to an `r1t`-typed destination.

   In 64-bit mode, binary instructions (ADD, SUB, CMP, TEST, AND, OR,
   XOR, IMUL2) only support sign-extended imm32 immediates. A 64-bit
   immediate that doesn't fit in that range must stay in a register.
*)
let combinable_imm r1t o = match o with
  | Oimm (i, `i64) when Type.equal_basic r1t `i64 ->
    Int64.(i >= -0x80000000L && i <= 0x7FFFFFFFL)
  | _ -> true

let collect_lea_mov fn =
  Func.fold_blks fn ~init:Ltree.empty ~f:(fun acc b ->
      let rec go acc = function
        | [] | [_] -> acc
        | (_, Two (LEA, Oreg (r1, _), Omem (Abd (b, d), _)))
          :: (l, Two (MOV, Oreg (r1', r1t), Oreg (r2', _)))
          :: xs when Rv.(b = r1') && Rv.(r1 = r2') ->
          let i = match d with
            | 1l -> One (INC, Oreg (r1', r1t))
            | _ ->
              let d = Int64.(of_int32 d land 0xFFFFFFFFL) in
              Two (ADD, Oreg (r1', r1t), Oimm (d, immty r1t)) in
          go (Ltree.set acc ~key:l ~data:i) xs
        | _ :: xs -> go acc xs in
      go acc @@ Seq.to_list @@ Seq.map ~f:decomp @@ Blk.insns b)

let lea_mov changed fn =
  map_insns changed fn @@ collect_lea_mov fn

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

let rset_mem' o l = List.exists l ~f:(Set.mem @@ rset [o])

let collect_mov_op fn =
  Func.fold_blks fn ~init:Ltree.empty ~f:(fun acc b ->
      let rec go acc = function
        | [] | [_] -> acc
        | (_, Two (MOV, Oreg (r1, _), o1))
          :: (_, Two (MOV, Oreg (r2, _), o2))
          :: (l, Two (op, Oreg (r3, r3t), Oreg (r3', _)))
          :: xs when combinable_binop op
                  && Rv.(r1 = r3')
                  && Rv.(r2 = r3)
                  && Rv.(r3 <> r3')
                  && not (Set.mem (rset [o1]) r1)
                  && not (rset_mem' o2 [r1; r2])
                  && combinable_imm r3t o1 ->
          let i = Two (op, Oreg (r3, r3t), o1) in
          go (Ltree.set acc ~key:l ~data:i) xs
        | (_, Two (MOV, Oreg (r1, _), o))
          :: (l, Two (op, Oreg (r1', r1t), Oreg (r2', _)))
          :: xs when combinable_binop op
                  && Rv.(r1 = r2')
                  && Rv.(r1' <> r2')
                  && not (Set.mem (rset [o]) r1)
                  && combinable_imm r1t o ->
          let i = Two (op, Oreg (r1', r1t), o) in
          go (Ltree.set acc ~key:l ~data:i) xs
        | (_, Two (MOV, Oreg (r1, _), o))
          :: (l, One (op, Oreg (r2', _)))
          :: xs when combinable_unop op
                  && Rv.(r1 = r2')
                  && not (Set.mem (rset [o]) r1) ->
          let i = One (op, o) in
          go (Ltree.set acc ~key:l ~data:i) xs
        | _ :: xs -> go acc xs in
      go acc @@ Seq.to_list @@ Seq.map ~f:decomp @@ Blk.insns b)

let mov_op changed fn =
  map_insns changed fn @@ collect_mov_op fn

let collect_mov_to_store fn =
  Func.fold_blks fn ~init:Ltree.empty ~f:(fun acc b ->
      let rec go acc = function
        | [] | [_] -> acc
        | (_, Two (MOV, Oreg (r1, r1t), (Oreg _ as r)))
          :: (l, Two (MOV, (Omem _ as o), Oreg (r2, r2t)))
          :: xs when Rv.(r1 = r2)
                  && Type.equal_basic r1t r2t ->
          let i = Two (MOV, o, r) in
          go (Ltree.set acc ~key:l ~data:i) xs
        | _ :: xs -> go acc xs in
      go acc @@ Seq.to_list @@ Seq.map ~f:decomp @@ Blk.insns b)

let mov_to_store changed fn =
  map_insns changed fn @@ collect_mov_to_store fn

let albl_of_op = function
  | Omem (Albl (l, _), _) -> Some l
  | _ -> None

let albl_of_insn = function
  | Two (_, a, b) -> List.filter_map [a; b] ~f:albl_of_op
  | One (_, a) -> Option.to_list (albl_of_op a)
  | JMP (Jind a) -> Option.to_list (albl_of_op a)
  | _ -> []

let collect_dead_fp_pseudos fn =
  let refs =
    Func.fold_blks fn ~init:Lset.empty ~f:(fun acc b ->
        Blk.insns b |> Seq.map ~f:Insn.insn |>
        Seq.fold ~init:acc ~f:(fun acc -> function
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
      let fn = dealloc_stack_before_leave changed fn in
      let fn = redundant_spill_after_reload changed fn in
      let fn = redundant_reload_after_spill changed fn in
      let fn = reuse_lea changed fn in
      let fn = and_test changed fn in
      let fn = lea_mov changed fn in
      let fn = mov_op changed fn in
      let fn = mov_to_store changed fn in
      let fn = remove_dead_fp_pseudos changed fn in
      if !changed then loop (i + 1) fn else fn in
  loop 1 fn
