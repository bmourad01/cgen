(* Helpers required by the implementations in [Regalloc]. *)

open Core
open X86_amd64_common
open Insn

(* XXX: any more cases than this? *)
let is_copy = function
  | Two (MOV, Oreg (d, td), Oreg (s, ts))
  | Two (MOVSS, Oreg (d, td), Oreg (s, ts))
  | Two (MOVSD, Oreg (d, td), Oreg (s, ts))
    when Type.equal_basic td ts -> Some (d, s)
  | _ -> None

let is_call = function
  | One (CALL _, _) -> true
  | _ -> false

let classof rv = match Regvar.which rv with
  | First r -> Reg.classof r
  | Second (_, cls) -> cls

let load_from_slot ty ~dst ~src = match classof dst with
  | GPR ->
    begin match ty with
      | `v128 | #Type.fp -> assert false
      | #Type.basic as b -> I.mov (Oreg (dst, b)) (Omem (Ab src, b))
    end
  | FP ->
    begin match ty with
      | `f64 -> I.movsd (Oreg (dst, `f64)) (Omem (Ab src, `i64))
      | `f32 -> I.movss (Oreg (dst, `f32)) (Omem (Ab src, `i32))
      | `v128 -> I.movdqa (Oregv dst) (Omem (Ab src, `v128))
      | #Type.imm -> assert false
    end

let move ty ~dst ~src = match classof dst with
  | GPR ->
    begin match ty with
      | `v128 | #Type.fp -> assert false
      | #Type.basic as b -> I.mov (Oreg (dst, b)) (Oreg (src, b))
    end
  | FP ->
    begin match ty with
      | `f64 -> I.movsd (Oreg (dst, `f64)) (Oreg (src, `f64))
      | `f32 -> I.movss (Oreg (dst, `f32)) (Oreg (src, `f32))
      | `v128 -> I.movdqa (Oregv dst) (Oregv src)
      | #Type.imm -> assert false
    end

let immty = function
  | #Type.imm as ty -> ty
  | _ -> assert false

let store_to_slot ty i ~src ~dst = match classof src with
  | GPR ->
    begin match ty with
      | `v128 | #Type.fp -> assert false
      | #Type.basic as b ->
        (* Attempt some peephole optimizations of the
           store. *)
        begin match i with
          (* XOR with self -> just store 0 in the slot *)
          | Two (XOR, Oreg (x, _), Oreg (y ,_))
            when Regvar.(x = y) && Regvar.(x = dst) ->
            I.mov (Omem (Ab dst, b)) (Oimm (0L, immty ty))
          | Two (SUB, Oreg (x, _), Oimm (1L, _))
            when Regvar.(x = dst) ->
            I.dec (Omem (Ab dst, b))
          | Two (ADD, Oreg (x, _), Oimm (1L, _))
            when Regvar.(x = dst) ->
            I.inc (Omem (Ab dst, b))
          | _ ->
            (* Default case: just do a regular store
               to the slot. *)
            I.mov (Omem (Ab dst, b)) (Oreg (src, b))
        end
    end
  | FP ->
    begin match ty with
      | `f64 -> I.movsd (Omem (Ab dst, `i64)) (Oreg (src, `f64))
      | `f32 -> I.movss (Omem (Ab dst, `i32)) (Oreg (src, `f32))
      | `v128 -> I.movdqa (Omem (Ab dst, `v128)) (Oregv src)
      | #Type.imm -> assert false
    end

let substitute_amode f = function
  | Ab b -> Ab (f b)
  | Abd (b, d) -> Abd (f b, d)
  | Abis (b, i, s) -> Abis (f b, f i, s)
  | Aisd (i, s, d) -> Aisd (f i, s, d)
  | Abisd (b, i, s, d) -> Abisd (f b, f i, s, d)
  | (Asym _ | Albl _) as a -> a

let substitute_operand f = function
  | Oreg (r, t) -> Oreg (f r, t)
  | Oregv v -> Oregv (f v)
  | Oimm _ as i -> i
  | Omem (a, ty) -> Omem (substitute_amode f a, ty)
  | Osym _ as s -> s
  | Oah -> Oah

(* Attempt some peephole optimizations after the substitution.
   XXX: what if the FLAGS register is live? *)
let substitute_binop' o a b op = match o, op a, op b with
  | LEA, Oreg (x, ty), Omem (Abd (y, d), _) when Regvar.(x = y) ->
    (* lea x, [x+d] => add x, d or sub x, -d *)
    if Int32.(d < 0l) then
      let d = Int32.neg d in
      let d' = Int64.(of_int32 d land 0xFFFFFFFFL) in
      if Int64.(d' = 1L) then
        One (DEC, Oreg (x, ty))
      else
        Two (SUB, Oreg (x, ty), Oimm (d', immty ty))
    else
      let d' = Int64.(of_int32 d land 0xFFFFFFFFL) in
      if Int64.(d' = 1L) then
        One (INC, Oreg (x, ty))
      else
        Two (ADD, Oreg (x, ty), Oimm (d', immty ty))
  | LEA, Oreg (x, ty), Omem (Abis (y, z, S1), _) when Regvar.(x = y) ->
    (* lea x, [x+y*1] => add x, y *)
    Two (ADD, Oreg (x, ty), Oreg (z, ty))
  | LEA, Oreg (x, ty), Omem (Abis (y, z, S1), _) when Regvar.(x = z) ->
    (* lea x, [y+x*1] => add x, y *)
    Two (ADD, Oreg (x, ty), Oreg (y, ty))
  | LEA, Oreg (x, ty), Omem (Aisd (y, S2, 0l), _) when Regvar.(x = y) ->
    (* lea x, [x*2] => shl x, 1 *)
    Two (SHL, Oreg (x, ty), Oimm (1L, `i8))
  | LEA, Oreg (x, ty), Omem (Aisd (y, S4, 0l), _) when Regvar.(x = y) ->
    (* lea x, [x*4] => shl x, 2 *)
    Two (SHL, Oreg (x, ty), Oimm (2L, `i8))
  | LEA, Oreg (x, ty), Omem (Aisd (y, S8, 0l), _) when Regvar.(x = y) ->
    (* lea x, [x*8] => shl x, 3 *)
    Two (SHL, Oreg (x, ty), Oimm (3L, `i8))
  | o, a, b ->
    (* Default case. *)
    Two (o, a, b)

let substitute' i op = match i with
  | One (o, a) -> One (o, op a)
  | Two (o, a, b) -> substitute_binop' o a b op
  | IMUL3 (a, b, c) -> IMUL3 (op a, op b, c)
  | JMP (Jind a) -> JMP (Jind (op a))
  | CDQ
  | CQO
  | CWD
  | Jcc _
  | JMP (Jlbl _)
  | RET
  | UD2
  | LEAVE
  | JMPtbl _
  | FP32 _
  | FP64 _ -> i

let substitute i f = substitute' i @@ substitute_operand f

module Typed_writes = struct
  type ty = [Type.basic | `v128]

  let wty ty = (ty :> ty)

  let reduce a b = match a, b with
    | (#Type.imm as ia), (#Type.imm as ib)
      when Type.sizeof_imm ia < Type.sizeof_imm ib -> b
    | #Type.imm, #Type.imm -> a
    | (#Type.fp as fa), (#Type.fp as fb)
      when Type.sizeof_fp fa < Type.sizeof_fp fb -> b
    | #Type.fp, #Type.fp -> a
    | `v128, `v128 -> `v128
    | _ -> assert false

  (* Helper for registers mentioned in an addressing mode. *)
  let rv_of_amode = function
    | Ab a -> [a, `i64]
    | Abd (a, _) -> [a, `i64]
    | Abis (a, b, _) -> [a, `i64; b, `i64]
    | Aisd (a, _, _) -> [a, `i64]
    | Abisd (a, b, _, _) -> [a, `i64; b, `i64]
    | Albl _ | Asym _ -> [Regvar.reg `rip, `i64]

  (* All registers mentioned in operands. *)
  let rmap operands =
    Regvar.Map.of_alist_reduce ~f:reduce @@
    List.bind operands ~f:(function
        | Oreg (a, t) -> [a, wty t]
        | Oregv a -> [a, `v128]
        | Omem (a, _) -> rv_of_amode a
        | Oah -> [Regvar.reg `rax, wty `i8]
        | _ -> [])

  (* Only explicit register operands. *)
  let rmap_reg operands =
    Regvar.Map.of_alist_reduce ~f:reduce @@
    List.bind operands ~f:(function
        | Oreg (a, t) -> [a, wty t]
        | Oregv a -> [a, `v128]
        | Oah -> [Regvar.reg `rax, `i8]
        | _ -> [])

  let rmap' l =
    Regvar.Map.of_alist_reduce ~f:reduce @@
    List.map l ~f:(fun (r, t) -> Regvar.reg r, t)

  let binop_writes o a _b = match o with
    | ADD
    | ADDSD
    | ADDSS
    | AND
    | BSF
    | BSR
    | CMOVcc _
    | CVTSD2SI
    | CVTTSD2SI
    | CVTSD2SS
    | CVTSI2SD
    | CVTSI2SS
    | CVTSS2SD
    | CVTSS2SI
    | CVTTSS2SI
    | DIVSD
    | DIVSS
    | IMUL2
    | LEA
    | MOV
    | MOV_
    | MOVD
    | MOVDQA
    | MOVQ
    | MOVSD
    | MOVSS
    | MOVSX
    | MOVSXD
    | MOVZX
    | MULSD
    | MULSS
    | OR
    | POPCNT
    | ROL
    | ROR
    | SAR
    | SHL
    | SHR
    | SUB
    | SUBSD
    | SUBSS
    | XOR
    | XORPD
    | XORPS
      -> rmap_reg [a]
    | CMP
    | TEST_
    | UCOMISD
    | UCOMISS
      -> Regvar.Map.empty

  let unop_writes call o a = match o with
    | CALL _
      -> call
    | DEC
    | INC
    | NEG
    | NOT
    | SETcc _
    | POP
      -> rmap_reg [a]
    | PUSH
      -> Regvar.Map.empty
    | DIV
    | IDIV
    | IMUL1
    | MUL ->
      begin match a with
        | Oreg (_, `i8)
          -> rmap' [`rax, `i8]
        | Oreg (_, t)
          -> rmap' [`rax, wty t; `rdx, wty t]
        | Omem (_, t)
          -> rmap' [`rax, wty t; `rdx, wty t]
        | _
          (* invalid forms *)
          -> Regvar.Map.empty
      end

  (* Registers written to by an instruction. *)
  let writes call = function
    | Two (o, a, b) -> binop_writes o a b
    | One (o, a) -> unop_writes call o a
    | IMUL3 (a, _, _)
      -> rmap_reg [a]
    | Jcc _
    | JMP _
    | JMPtbl _
    | FP32 _
    | FP64 _
    | RET
    | UD2
      -> Regvar.Map.empty
    | CDQ
      -> rmap' [`rdx, `i32]
    | CQO
      -> rmap' [`rdx, `i64]
    | CWD
      -> rmap' [`rdx, `i16]
    | LEAVE
      -> rmap' [`rsp, `i64; `rbp, `i64]
end

let writes_with_types = Typed_writes.writes

module Pre_assign_slots(C : Context_intf.S) = struct
  open C.Syntax

  let freshen x off =
    let+ x' = C.Var.fresh >>| Regvar.var GPR in
    x', [I.lea (Oreg (x', `i64)) (Omem (Abd (x, off), `i64))]

  let add_disp base off d =
    let off' = Int32.of_int_exn off in
    let d' = Int32.(d + off') in
    if (off > 0 && Int32.(d' < d)) ||
       (off < 0 && Int32.(d' > d)) then
      let+ x, is = freshen base off' in
      Second (x, is)
    else !!(First d')

  let assign_ab find base a b = match find b with
    | Some 0 -> !!(Ab base, [])
    | Some o -> !!(Abd (base, Int32.of_int_exn o), [])
    | None -> !!(a, [])

  let assign_abd find base a b d = match find b with
    | None -> !!(a, [])
    | Some o -> add_disp base o d >>| function
      | First d' -> Abd (base, d'), []
      | Second (b', bi) -> Abd (b', d), bi

  let assign_abis find base a b i s = match find b, find i with
    | None, None -> !!(a, [])
    | Some 0, None -> !!(Abis (base, i, s), [])
    | Some o, None -> !!(Abisd (base, i, s, Int32.of_int_exn o), [])
    | None, Some o ->
      let+ i', ii = freshen base (Int32.of_int_exn o) in
      Abis (b, i', s), ii
    | Some ob, Some oi ->
      let+ i', ii = freshen base (Int32.of_int_exn oi) in
      Abisd (base, i', s, Int32.of_int_exn ob), ii

  let assign_aisd find base a i s d = match find i with
    | None -> !!(a, [])
    | Some o ->
      let+ i', ii = freshen base (Int32.of_int_exn o) in
      Aisd (i', s, d), ii

  let rec assign_amode find base a = match a with
    | Albl _ | Asym _ -> !!(a, [])
    | Ab b -> assign_ab find base a b
    | Abd (b, d) -> assign_abd find base a b d
    | Abis (b, i, s) -> assign_abis find base a b i s
    | Aisd (i, S1, d) -> assign_amode find base @@ Abd (i, d)
    | Aisd (i, s, d) -> assign_aisd find base a i s d
    | Abisd (b, i, s, d) -> assign_abisd find base a b i s d

  and assign_abisd find base a b i s d = match find b, find i with
    | None, None -> !!(a, [])
    | None, Some _ when equal_scale s S1 ->
      assign_amode find base @@ Abisd (i, b, S1, d)
    | None, Some o ->
      let+ i', ii = freshen base (Int32.of_int_exn o) in
      Abisd (b, i', s, d), ii
    | Some o, None ->
      begin add_disp base o d >>| function
        | First d' -> Abisd (base, i, s, d'), []
        | Second (b', bi) -> Abisd (b', i, s, d), bi
      end
    | Some ob, Some oi ->
      let* i', ii = freshen base (Int32.of_int_exn oi) in
      add_disp base ob d >>| function
      | First d' -> Abisd (base, i', s, d'), ii
      | Second (b', bi) -> Abisd (b', i', s, d), bi @ ii

  let assign_operand find base op = match op with
    | Oreg (r, t) ->
      (* XXX: let's hope that a slot doesn't appear here if this is a
         destination register. *)
      begin match find r with
        | None -> !!(op, [])
        | Some o ->
          let+ r', ri = freshen base (Int32.of_int_exn o) in
          Oreg (r', t), ri
      end
    | Oregv r ->
      begin match find r with
        | None -> !!(op, [])
        | Some _ -> assert false (* ill-typed *)
      end
    | Omem (a, ty) ->
      let+ a', ai = assign_amode find base a in
      Omem (a', ty), ai
    | _ -> !!(op, [])

  let assign find base i =
    let op = assign_operand find base in
    match i with
    | One (o, a) ->
      let+ a, ai = op a in
      ai @ [One (o, a)]
    | Two (o, a, b) ->
      let* a, ai = op a in
      let+ b, bi = op b in
      ai @ bi @ [Two (o, a, b)]
    | IMUL3 (a, b, c) ->
      let* a, ai = op a in
      let+ b, bi = op b in
      ai @ bi @ [IMUL3 (a, b, c)]
    | JMP (Jind a) ->
      let+ a, ai = op a in
      ai @ [JMP (Jind a)]
    | CDQ
    | CQO
    | CWD
    | Jcc _
    | JMP (Jlbl _)
    | RET
    | UD2
    | LEAVE
    | JMPtbl _
    | FP32 _
    | FP64 _ -> !![i]
end

(* NB: this makes assumptions based on the results of `Pre_assign_slots`. *)
module Post_assign_slots = struct
  (* All spills/reloads should be using this form. *)
  let assign_ab find base a b = match find b with
    | Some 0 -> Ab base
    | Some o -> Abd (base, Int32.of_int_exn o)
    | None -> a

  let assign_abd find base a b _d = match find b with
    | None -> a
    | Some _ -> assert false

  let assign_abis find base a b i _s = match find b, find i with
    | None, None -> a
    | Some _, None -> assert false
    | None, Some _ -> assert false
    | Some _, Some _ -> assert false

  let assign_aisd find base a i _s _d = match find i with
    | None -> a
    | Some _ -> assert false

  let assign_abisd find base a b i _s _d = match find b, find i with
    | None, None -> a
    | None, Some _ -> assert false
    | Some _, Some _ -> assert false
    | Some _, None -> assert false

  let assign_amode find base a = match a with
    | Albl _ | Asym _ -> a
    | Ab b -> assign_ab find base a b
    | Abd (b, d) -> assign_abd find base a b d
    | Abis (b, i, s) -> assign_abis find base a b i s
    | Aisd (i, s, d) -> assign_aisd find base a i s d
    | Abisd (b, i, s, d) -> assign_abisd find base a b i s d

  let assign_operand find base op = match op with
    | Oreg (r, _) ->
      begin match find r with
        | None -> op
        | Some _ -> assert false
      end
    | Oregv r ->
      begin match find r with
        | None -> op
        | Some _ -> assert false
      end
    | Omem (a, ty) -> Omem (assign_amode find base a, ty)
    | _ -> op

  let assign find base i = substitute' i @@ assign_operand find base
end

let post_assign_slots = Post_assign_slots.assign

let align8 i = (i + 7) land -8
let odd i = (i land 1) <> 0
let is16 i = (i land 15) = 0

(* Pad the stack to account for:

   1. The return address already on the stack upon entry.
   2. The callee-save registers being pushed to the stack.
*)
let adjust_sp_size regs size = match List.length regs with
  | 0 when size = 0 ->
    (* If we're not allocating any slots, and we have no
       callee-save registers to preserve, then the stack
       pointer does not need to be aligned.

       There is a consideration for instructions that
       require aligned memory access (such as MOVDQA),
       but this should be handled by the instruction
       selection pass.
    *)
    0
  | 0 when is16 size -> size + 8
  | 0 -> size
  | n when odd n && is16 size -> size
  | n when odd n -> size + 8
  | _ when is16 size -> size + 8
  | _ -> size

let no_frame_prologue regs size =
  let size = Int64.of_int @@ adjust_sp_size regs @@ align8 size in
  let rsp = Oreg (Regvar.reg `rsp, `i64) in
  List.concat [
    List.map regs ~f:(fun r ->
        I.push (Oreg (Regvar.reg r, `i64)));
    (if Int64.(size = 0L) then []
     else [I.sub rsp (Oimm (size, `i64))]);
  ]

let no_frame_epilogue regs size =
  let size = Int64.of_int @@ adjust_sp_size regs @@ align8 size in
  let rsp = Oreg (Regvar.reg `rsp, `i64) in
  List.concat [
    (if Int64.(size = 0L) then []
     else [I.add rsp (Oimm (size, `i64))]);
    List.rev regs |> List.map ~f:(fun r ->
        I.pop (Oreg (Regvar.reg r, `i64)));
  ]

(* Same as above, but with the added factor of the frame
   pointer being pushed to the stack.

   This amounts to adding 8 in the opposite cases.
*)
let adjust_fp_size regs size = match List.length regs with
  | 0 when is16 size -> size
  | 0 when size = 8 ->
    (* Same as below. *)
    0
  | 0 -> size + 8
  | n when odd n && is16 size -> size + 8
  | n when odd n -> size
  | _ when is16 size -> size
  | _ when size = 8 ->
    (* In this case, the stack pointer is already aligned, and
       the size of 8 already accounts for preserving the frame
       pointer, so we don't need to adjust the stack pointer
       at all. *)
    0
  | _ -> size + 8

let frame_prologue regs size =
  let size = Int64.of_int @@ adjust_fp_size regs @@ align8 size in
  let rsp = Oreg (Regvar.reg `rsp, `i64) in
  let rbp = Oreg (Regvar.reg `rbp, `i64) in
  List.concat [
    (* Push the frame pointer and give it the base of the stack. *)
    [I.push rbp;
     I.mov rbp rsp];
    (* Allocate space. *)
    (if Int64.(size = 0L) then []
     else [I.sub rsp (Oimm (size, `i64))]);
    (* Push the callee-save registers. *)
    List.map regs ~f:(fun r ->
        I.push (Oreg (Regvar.reg r, `i64)));
  ]

let frame_epilogue regs _size =
  List.concat [
    (* Pop the callee-save registers in reverse order. *)
    List.rev regs |> List.map ~f:(fun r ->
        I.pop (Oreg (Regvar.reg r, `i64)));
    (* Deallocate the space and pop the frame pointer. *)
    [I.leave];
  ]
