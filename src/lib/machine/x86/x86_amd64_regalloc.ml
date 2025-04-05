(* Helpers required by the implementations in [Regalloc]. *)

open Core
open X86_amd64_common
open Insn

(* XXX: any more cases than this? *)
let copy = function
  | Two (MOV, Oreg (d, td), Oreg (s, ts))
  | Two (MOVSS, Oreg (d, td), Oreg (s, ts))
  | Two (MOVSD, Oreg (d, td), Oreg (s, ts))
    when Type.equal_basic td ts -> Some (d, s)
  | _ -> None

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

let store_to_slot ty ~src ~dst = match classof src with
  | GPR ->
    begin match ty with
      | `v128 | #Type.fp -> assert false
      | #Type.basic as b -> I.mov (Omem (Ab dst, b)) (Oreg (src, b))
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

let substitute' i op = match i with
  | One (o, a) -> One (o, op a)
  | Two (o, a, b) -> Two (o, op a, op b)
  | IMUL3 (a, b, c) -> IMUL3 (op a, op b, c)
  | JMP (Jind a) -> JMP (Jind (op a))
  | CDQ
  | CQO
  | CWD
  | Jcc _
  | JMP (Jlbl _)
  | RET
  | UD2
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

  (* Registers written to by an instruction. *)
  let writes call = function
    | Two (o, a, _) ->
      begin match o with
        | ADD
        | ADDSD
        | ADDSS
        | AND
        | CMOVcc _
        | CVTSD2SI
        | CVTSD2SS
        | CVTSI2SD
        | CVTSI2SS
        | CVTSS2SD
        | CVTSS2SI
        | DIVSD
        | DIVSS
        | IMUL2
        | LEA
        | LZCNT
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
        | TZCNT
        | XOR
        | XORPD
        | XORPS
          -> rmap_reg [a]
        | CMP
        | TEST_
        | UCOMISD
        | UCOMISS
          -> Regvar.Map.empty
      end
    | One (o, a) ->
      begin match o with
        | CALL
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
      end
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
end

let writes_with_types = Typed_writes.writes

(* A few points here:

   1. Slots appearing in operands will need to refer to their
      assigned stack location later, so we need to insert some
      admininstrative code.

   2. Slots appearing in an addressing mode in the presence of
      an existing displacement will need this treatment as well,
      because we want to avoid overflowing the displacement (which
      is a signed 32-bit immediate).

   3. Slots appearing as an index register in the addressing mode
      will also need this, because the index register is scaled.
*)
module Replace_direct_slot_uses(C : Context_intf.S) = struct
  open C.Syntax

  let freshen is_slot x = if is_slot x then
      let+ x' = C.Var.fresh >>| Regvar.var GPR in
      x', [I.lea (Oreg (x', `i64)) (Omem (Ab x, `i64))]
    else !!(x, [])

  let replace_amode is_slot a = match a with
    | Ab _ | Albl _ | Asym _ | Abd _ -> !!(a, [])
    | Abis (b, i, s) ->
      let+ i', ii = freshen is_slot i in
      Abis (b, i', s), ii
    | Aisd (i, s, d) ->
      let+ i', ii = freshen is_slot i in
      Aisd (i', s, d), ii
    | Abisd (b, i, s, d) ->
      let+ i', ii = freshen is_slot i in
      Abisd (b, i', s, d), ii

  let replace_operand is_slot op = match op with
    | Oreg (r, ty) ->
      (* XXX: let's hope that a slot doesn't appear here if this is a
         destination register. *)
      let+ r', ri = freshen is_slot r in
      Oreg (r', ty), ri
    | Omem (a, ty) ->
      let+ a, ai = replace_amode is_slot a in
      Omem (a, ty), ai
    | _ -> !!(op, [])

  let replace is_slot i =
    let op = replace_operand is_slot in
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
    | JMPtbl _
    | FP32 _
    | FP64 _ -> !![i]
end

module Assign_slots = struct
  let find offsets rv = match Regvar.which rv with
    | Second (v, _) -> Map.find offsets v
    | First _ -> None

  let add_disp off d =
      let d' = Int32.(d + of_int_exn off) in
      (* We can't easily predict whether this will overflow or not ahead of time,
         because we don't know what the stack layout will be, so it seems fair to
         alert the user that their code is likely to be wrong. *)
      if (off > 0 && Int32.(d' < d)) ||
         (off < 0 && Int32.(d' > d)) then
        failwithf "Overflow when adjusting displacement with stack \
                   offset 0x%x (pre: 0x%lx, post: 0x%lx)"
          off d d' ();
      d'

  (* NB: this makes assumptions based on the results of `Replace_direct_slot_uses`. *)
  let assign_amode base offsets a = match a with
    | Albl _ | Asym _ -> a
    | Ab b ->
      begin match find offsets b with
        | Some 0 -> Ab base
        | Some o -> Abd (base, Int32.of_int_exn o)
        | None -> a
      end
    | Abd (b, d) ->
      begin match find offsets b with
        | None -> a
        | Some o -> Abd (base, add_disp o d)
      end
    | Abis (b, i, s) ->
      begin match find offsets b, find offsets i with
        | None, None -> a
        | Some 0, None -> Abis (base, i, s)
        | Some o, None -> Abisd (base, i, s, Int32.of_int_exn o)
        | None, Some _ -> assert false
        | Some _, Some _ -> assert false
      end
    | Aisd (i, _s, _d) ->
      begin match find offsets i with
        | None -> a
        | Some _ -> assert false
      end
    | Abisd (b, i, s, d) ->
      begin match find offsets b, find offsets i with
        | None, None -> a
        | Some o, None -> Abisd (base, i, s, add_disp o d)
        | None, Some _ -> assert false
        | Some _, Some _ -> assert false
      end

  let assign_operand base offsets op = match op with
    | Oreg (r, _) ->
      begin match find offsets r with
        | None -> op
        | Some _ -> assert false
      end
    | Oregv r ->
      begin match find offsets r with
        | None -> op
        | Some _ -> assert false
      end
    | Omem (a, ty) -> Omem (assign_amode base offsets a, ty)
    | _ -> op

  let assign base offsets i =
    let base = Regvar.reg base in
    substitute' i @@ assign_operand base offsets
end

let assign_slots = Assign_slots.assign

let align8 i = (i + 7) land -8
let odd i = (i land 1) <> 0
let is16 i = (i land 15) = 0

(* Pad the stack to account for:

   1. The return address already on the stack upon entry.
   2. The callee-save registers being pushed to the stack.
*)
let adjust_sp_size regs size = match List.length regs with
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
  | 0 -> size + 8
  | n when odd n && is16 size -> size + 8
  | n when odd n -> size
  | _ when is16 size -> size
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

let frame_epilogue regs size =
  let size = Int64.of_int @@ adjust_fp_size regs @@ align8 size in
  let rsp = Oreg (Regvar.reg `rsp, `i64) in
  let rbp = Oreg (Regvar.reg `rbp, `i64) in
  List.concat [
    (* Pop the callee-save registers in reverse order. *)
    List.rev regs |> List.map ~f:(fun r ->
        I.pop (Oreg (Regvar.reg r, `i64)));
    (* Deallocate space. *)
    (if Int64.(size = 0L) then []
     else [I.add rsp (Oimm (size, `i64))]);
    (* Pop the frame pointer. *)
    [I.pop rbp];
  ]
