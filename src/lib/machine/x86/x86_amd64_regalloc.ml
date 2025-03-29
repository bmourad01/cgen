(* Helpers required by the implementations in [Regalloc]. *)

open Core
open X86_amd64_common
open Insn

(* XXX: any more cases than this? *)
let copy = function
  | MOV (Oreg (d, td), Oreg (s, ts))
  | MOVSS (Oreg (d, td), Oreg (s, ts))
  | MOVSD (Oreg (d, td), Oreg (s, ts))
    when Type.equal_basic td ts -> Some (d, s)
  | _ -> None

let classof rv = match Regvar.which rv with
  | First r -> Reg.classof r
  | Second (_, cls) -> cls

let load_from_slot ty ~dst ~src = match classof dst with
  | GPR ->
    begin match ty with
      | `v128 | #Type.fp -> assert false
      | #Type.basic as b -> MOV (Oreg (dst, b), Omem (Ab src, b))
    end
  | FP ->
    begin match ty with
      | `f64 -> MOVSD (Oreg (dst, `f64), Omem (Ab src, `i64))
      | `f32 -> MOVSS (Oreg (dst, `f32), Omem (Ab src, `i32))
      | `v128 -> MOVDQA (Oregv dst, Omem (Ab src, `v128))
      | #Type.imm -> assert false
    end

let store_to_slot ty ~src ~dst = match classof src with
  | GPR ->
    begin match ty with
      | `v128 | #Type.fp -> assert false
      | #Type.basic as b -> MOV (Omem (Ab dst, b), Oreg (src, b))
    end
  | FP ->
    begin match ty with
      | `f64 -> MOVSD (Omem (Ab dst, `i64), Oreg (src, `f64))
      | `f32 -> MOVSD (Omem (Ab dst, `i32), Oreg (src, `f32))
      | `v128 -> MOVDQA (Omem (Ab dst, `v128), Oregv src)
      | #Type.imm -> assert false
    end

let substitute_amode f = function
  | Ad _ as a -> a
  | Ab b -> Ab (f b)
  | Abd (b, d) -> Abd (f b, d)
  | Abis (b, i, s) -> Abis (f b, f i, s)
  | Aisd (i, s, d) -> Aisd (f i, s, d)
  | Abisd (b, i, s, d) -> Abisd (f b, f i, s, d)

let substitute_operand f = function
  | Oreg (r, t) -> Oreg (f r, t)
  | Oregv v -> Oregv (f v)
  | Oimm _ as i -> i
  | Omem (a, ty) -> Omem (substitute_amode f a, ty)
  | Osym _ as s -> s
  | Ofp32 _ as s -> s
  | Ofp64 _ as d -> d
  | Oah -> Oah

let substitute' i op = match i with
  | ADD (a, b) -> ADD (op a, op b)
  | ADDSD (a, b) -> ADDSD (op a, op b)
  | ADDSS (a, b) -> ADDSS (op a, op b)
  | AND (a, b) -> AND (op a, op b)
  | CALL a -> CALL (op a)
  | CDQ -> i
  | CMOVcc (cc, a, b) -> CMOVcc (cc, op a, op b)
  | CMP (a, b) -> CMP (op a, op b)
  | CQO -> i
  | CWD -> i
  | CVTSD2SI (a, b) -> CVTSD2SI (op a, op b)
  | CVTSD2SS (a, b) -> CVTSD2SS (op a, op b)
  | CVTSI2SD (a, b) -> CVTSI2SD (op a, op b)
  | CVTSI2SS (a, b) -> CVTSI2SS (op a, op b)
  | CVTSS2SI (a, b) -> CVTSS2SI (op a, op b)
  | CVTSS2SD (a, b) -> CVTSS2SD (op a, op b)
  | DEC a -> DEC (op a)
  | DIV a -> DIV (op a)
  | DIVSD (a, b) -> DIVSD (op a, op b)
  | DIVSS (a, b) -> DIVSS (op a, op b)
  | IDIV a -> IDIV (op a)
  | IMUL1 a -> IMUL1 (op a)
  | IMUL2 (a, b) -> IMUL2 (op a, op b)
  | IMUL3 (a, b, c) -> IMUL3 (op a, op b, c)
  | INC a -> INC (op a)
  | Jcc _  -> i
  | JMP (Jind a) -> JMP (Jind (op a))
  | JMP (Jlbl _) -> i
  | LEA (a, b) -> LEA (op a, op b)
  | LZCNT (a, b) -> LZCNT (op a, op b)
  | MOV (a, b) -> MOV (op a, op b)
  | MOVD (a, b) -> MOVD (op a, op b)
  | MOVDQA (a, b) -> MOVDQA (op a, op b)
  | MOVQ (a, b) -> MOVQ (op a, op b)
  | MOVSD (a, b) -> MOVSD (op a, op b)
  | MOVSS (a, b) -> MOVSS (op a, op b)
  | MOVSX (a, b) -> MOVSX (op a, op b)
  | MOVSXD (a, b) -> MOVSXD (op a, op b)
  | MOVZX (a, b) -> MOVZX (op a, op b)
  | MUL a -> MUL (op a)
  | MULSD (a, b) -> MULSD (op a, op b)
  | MULSS (a, b) -> MULSS (op a, op b)
  | NEG a -> NEG (op a)
  | NOT a -> NOT (op a)
  | OR (a, b) -> OR (op a, op b)
  | POP a -> POP (op a)
  | POPCNT (a, b) -> POPCNT (op a, op b)
  | PUSH a -> PUSH (op a)
  | RET -> i
  | ROL (a, b) -> ROL (op a, op b)
  | ROR (a, b) -> ROR (op a, op b)
  | SAR (a, b) -> SAR (op a, op b)
  | SETcc (cc, a) -> SETcc (cc, op a)
  | SHL (a, b) -> SHL (op a, op b)
  | SHR (a, b) -> SHR (op a, op b)
  | SUB (a, b) -> SUB (op a, op b)
  | SUBSD (a, b) -> SUBSD (op a, op b)
  | SUBSS (a, b) -> SUBSS (op a, op b)
  | TEST_ (a, b) -> TEST_ (op a, op b)
  | TZCNT (a, b) -> TZCNT (op a, op b)
  | UCOMISD (a, b) -> UCOMISD (op a, op b)
  | UCOMISS (a, b) -> UCOMISS (op a, op b)
  | UD2 -> i
  | XOR (a, b) -> XOR (op a, op b)
  | XORPD (a, b) -> XORPD (op a, op b)
  | XORPS (a, b) -> XORPS (op a, op b)
  | MOV_ (a, b) -> MOV_ (op a, op b)
  | JMPtbl _ -> i

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
    | Ad _ -> []
    | Ab a -> [a, `i64]
    | Abd (a, _) -> [a, `i64]
    | Abis (a, b, _) -> [a, `i64; b, `i64]
    | Aisd (a, _, _) -> [a, `i64]
    | Abisd (a, b, _, _) -> [a, `i64; b, `i64]

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
    | ADD (a, _)
    | AND (a, _)
    | DEC a
    | IMUL2 (a, _)
    | IMUL3 (a, _, _)
    | INC a
    | LZCNT (a, _)
    | NEG a
    | NOT a
    | OR (a, _)
    | POPCNT (a, _)
    | ROL (a, _)
    | ROR (a, _)
    | SAR (a, _)
    | SHL (a, _)
    | SHR (a, _)
    | SUB (a, _)
    | XOR (a, _)
      -> rmap_reg [a]
    | ADDSD (a, _)
    | ADDSS (a, _)
    | CMOVcc (_, a, _)
    | CVTSD2SI (a, _)
    | CVTSD2SS (a, _)
    | CVTSI2SD (a, _)
    | CVTSI2SS (a, _)
    | CVTSS2SI (a, _)
    | CVTSS2SD (a, _)
    | DIVSD (a, _)
    | DIVSS (a, _)
    | LEA (a, _)
    | MOV (a, _)
    | MOV_ (a, _)
    | MOVD (a, _)
    | MOVDQA (a, _)
    | MOVQ (a, _)
    | MOVSD (a, _)
    | MOVSS (a, _)
    | MOVSX (a, _)
    | MOVSXD (a, _)
    | MOVZX (a, _)
    | MULSD (a, _)
    | MULSS (a, _)
    | SETcc (_, a)
    | SUBSD (a, _)
    | SUBSS (a, _)
    | TZCNT (a, _)
    | XORPD (a, _)
    | XORPS (a, _)
      -> rmap_reg [a]
    | CALL _
      -> call
    | PUSH _
    | RET
      -> Regvar.Map.empty
    | CMP _
    | TEST_ _
    | UCOMISD _
    | UCOMISS _
      -> Regvar.Map.empty
    | Jcc _
    | JMP _
    | UD2
    | JMPtbl _
      -> Regvar.Map.empty
    (* Special case for 8-bit div/mul. *)
    | DIV Oreg (_, `i8)
    | IDIV Oreg (_, `i8)
    | IMUL1 Oreg (_, `i8)
    | MUL Oreg (_, `i8)
      -> rmap' [`rax, `i8]
    | CDQ
      -> rmap' [`rdx, `i32]
    | CQO
      -> rmap' [`rdx, `i64]
    | CWD
      -> rmap' [`rdx, `i16]
    | DIV (Oreg (_, t))
    | IDIV (Oreg (_, t))
    | IMUL1 (Oreg (_, t))
    | MUL (Oreg (_, t))
      -> rmap' [`rax, wty t; `rdx, wty t]
    | DIV (Omem (_, t))
    | IDIV (Omem (_, t))
    | IMUL1 (Omem (_, t))
    | MUL (Omem (_, t))
      -> rmap' [`rax, wty t; `rdx, wty t]
    (* These are invalid forms. *)
    | DIV _
    | IDIV _
    | IMUL1 _
    | MUL _
      -> Regvar.Map.empty
    | POP a
      -> rmap_reg [a]
end

let writes_with_types = Typed_writes.writes

module Replace_direct_slot_uses(C : Context_intf.S) = struct
  open C.Syntax

  let replace_amode is_slot a = match a with
    | Abis (b, i, s) when is_slot i ->
      let+ x = C.Var.fresh >>| Regvar.var GPR in
      Abis (b, x, s), [LEA (Oreg (x, `i64), Omem (Ab i, `i64))]
    | Aisd (i, s, d) when is_slot i ->
      let+ x = C.Var.fresh >>| Regvar.var GPR in
      Aisd (x, s, d), [LEA (Oreg (x, `i64), Omem (Ab i, `i64))]
    | Abisd (b, i, s, d) when is_slot i ->
      let+ x = C.Var.fresh >>| Regvar.var GPR in
      Abisd (b, x, s, d), [LEA (Oreg (x, `i64), Omem (Ab i, `i64))]
    | _ -> !!(a, [])

  let replace_operand is_slot op = match op with
    | Oreg (r, ty) when is_slot r ->
      let+ x = C.Var.fresh >>| Regvar.var GPR in
      Oreg (x, ty), [LEA (Oreg (x, ty), Omem (Ab r, `i64))]
    | Oreg _ -> !!(op, [])
    | Omem (a, ty) ->
      let+ a, ai = replace_amode is_slot a in
      Omem (a, ty), ai
    | _ -> !!(op, [])

  let replace is_slot i =
    let op = replace_operand is_slot in
    match i with
    | ADD (a, b) ->
      let* a, ai = op a in
      let+ b, bi = op b in
      ai @ bi @ [ADD (a, b)]
    | ADDSD (a, b) ->
      let* a, ai = op a in
      let+ b, bi = op b in
      ai @ bi @ [ADDSD (a, b)]
    | ADDSS (a, b) ->
      let* a, ai = op a in
      let+ b, bi = op b in
      ai @ bi @ [ADDSS (a, b)]
    | AND (a, b) ->
      let* a, ai = op a in
      let+ b, bi = op b in
      ai @ bi @ [AND (a, b)]
    | CALL a ->
      let+ a, ai = op a in
      ai @ [CALL a]
    | CDQ -> !![i]
    | CMOVcc (cc, a, b) ->
      let* a, ai = op a in
      let+ b, bi = op b in
      ai @ bi @ [CMOVcc (cc, a, b)]
    | CMP (a, b) ->
      let* a, ai = op a in
      let+ b, bi = op b in
      ai @ bi @ [CMP (a, b)]
    | CQO -> !![i]
    | CWD -> !![i]
    | CVTSD2SI (a, b) ->
      let* a, ai = op a in
      let+ b, bi = op b in
      ai @ bi @ [CVTSD2SI (a, b)]
    | CVTSD2SS (a, b) ->
      let* a, ai = op a in
      let+ b, bi = op b in
      ai @ bi @ [CVTSD2SS (a, b)]
    | CVTSI2SD (a, b) ->
      let* a, ai = op a in
      let+ b, bi = op b in
      ai @ bi @ [CVTSI2SD (a, b)]
    | CVTSI2SS (a, b) ->
      let* a, ai = op a in
      let+ b, bi = op b in
      ai @ bi @ [CVTSI2SS (a, b)]
    | CVTSS2SD (a, b) ->
      let* a, ai = op a in
      let+ b, bi = op b in
      ai @ bi @ [CVTSS2SD (a, b)]
    | CVTSS2SI (a, b) ->
      let* a, ai = op a in
      let+ b, bi = op b in
      ai @ bi @ [CVTSS2SI (a, b)]
    | DEC a ->
      let+ a, ai = op a in
      ai @ [DEC a]
    | DIV a ->
      let+ a, ai = op a in
      ai @ [DIV a]
    | DIVSD (a, b) ->
      let* a, ai = op a in
      let+ b, bi = op b in
      ai @ bi @ [DIVSD (a, b)]
    | DIVSS (a, b) ->
      let* a, ai = op a in
      let+ b, bi = op b in
      ai @ bi @ [DIVSS (a, b)]
    | IDIV a ->
      let+ a, ai = op a in
      ai @ [IDIV a]
    | IMUL1 a ->
      let+ a, ai = op a in
      ai @ [IDIV a]
    | IMUL2 (a, b) ->
      let* a, ai = op a in
      let+ b, bi = op b in
      ai @ bi @ [IMUL2 (a, b)]
    | IMUL3 (a, b, c) ->
      let* a, ai = op a in
      let+ b, bi = op b in
      ai @ bi @ [IMUL3 (a, b, c)]
    | INC a ->
      let+ a, ai = op a in
      ai @ [INC a]
    | Jcc _ -> !![i]
    | JMP (Jind a) ->
      let+ a, ai = op a in
      ai @ [JMP (Jind a)]
    | JMP (Jlbl _) -> !![i]
    | LEA (a, b) ->
      let* a, ai = op a in
      let+ b, bi = op b in
      ai @ bi @ [LEA (a, b)]
    | LZCNT (a, b) ->
      let* a, ai = op a in
      let+ b, bi = op b in
      ai @ bi @ [LZCNT (a, b)]
    | MOV (a, b) ->
      let* a, ai = op a in
      let+ b, bi = op b in
      ai @ bi @ [MOV (a, b)]
    | MOVD (a, b) ->
      let* a, ai = op a in
      let+ b, bi = op b in
      ai @ bi @ [MOVD (a, b)]
    | MOVDQA (a, b) ->
      let* a, ai = op a in
      let+ b, bi = op b in
      ai @ bi @ [MOVDQA (a, b)]
    | MOVQ (a, b) ->
      let* a, ai = op a in
      let+ b, bi = op b in
      ai @ bi @ [MOVQ (a, b)]
    | MOVSD (a, b) ->
      let* a, ai = op a in
      let+ b, bi = op b in
      ai @ bi @ [MOVSD (a, b)]
    | MOVSS (a, b) ->
      let* a, ai = op a in
      let+ b, bi = op b in
      ai @ bi @ [MOVSS (a, b)]
    | MOVSX (a, b) ->
      let* a, ai = op a in
      let+ b, bi = op b in
      ai @ bi @ [MOVSX (a, b)]
    | MOVSXD (a, b) ->
      let* a, ai = op a in
      let+ b, bi = op b in
      ai @ bi @ [MOVSXD (a, b)]
    | MOVZX (a, b) ->
      let* a, ai = op a in
      let+ b, bi = op b in
      ai @ bi @ [MOVZX (a, b)]
    | MUL a ->
      let+ a, ai = op a in
      ai @ [MUL a]
    | MULSD (a, b) ->
      let* a, ai = op a in
      let+ b, bi = op b in
      ai @ bi @ [MULSD (a, b)]
    | MULSS (a, b) ->
      let* a, ai = op a in
      let+ b, bi = op b in
      ai @ bi @ [MULSS (a, b)]
    | NEG a ->
      let+ a, ai = op a in
      ai @ [NEG a]
    | NOT a ->
      let+ a, ai = op a in
      ai @ [NOT a]
    | OR (a, b) ->
      let* a, ai = op a in
      let+ b, bi = op b in
      ai @ bi @ [OR (a, b)]
    | POP a ->
      let+ a, ai = op a in
      ai @ [POP a]
    | POPCNT (a, b) ->
      let* a, ai = op a in
      let+ b, bi = op b in
      ai @ bi @ [POPCNT (a, b)]
    | PUSH a ->
      let+ a, ai = op a in
      ai @ [PUSH a]
    | RET -> !![i]
    | ROL (a, b) ->
      let* a, ai = op a in
      let+ b, bi = op b in
      ai @ bi @ [ROL (a, b)]
    | ROR (a, b) ->
      let* a, ai = op a in
      let+ b, bi = op b in
      ai @ bi @ [ROR (a, b)]
    | SAR (a, b) ->
      let* a, ai = op a in
      let+ b, bi = op b in
      ai @ bi @ [SAR (a, b)]
    | SETcc (cc, a) ->
      let+ a, ai = op a in
      ai @ [SETcc (cc, a)]
    | SHL (a, b) ->
      let* a, ai = op a in
      let+ b, bi = op b in
      ai @ bi @ [SHL (a, b)]
    | SHR (a, b) ->
      let* a, ai = op a in
      let+ b, bi = op b in
      ai @ bi @ [SHR (a, b)]
    | SUB (a, b) ->
      let* a, ai = op a in
      let+ b, bi = op b in
      ai @ bi @ [SUB (a, b)]
    | SUBSD (a, b) ->
      let* a, ai = op a in
      let+ b, bi = op b in
      ai @ bi @ [SUBSD (a, b)]
    | SUBSS (a, b) ->
      let* a, ai = op a in
      let+ b, bi = op b in
      ai @ bi @ [SUBSS (a, b)]
    | TEST_ (a, b) ->
      let* a, ai = op a in
      let+ b, bi = op b in
      ai @ bi @ [TEST_ (a, b)]
    | TZCNT (a, b) ->
      let* a, ai = op a in
      let+ b, bi = op b in
      ai @ bi @ [TZCNT (a, b)]
    | UCOMISD (a, b) ->
      let* a, ai = op a in
      let+ b, bi = op b in
      ai @ bi @ [UCOMISD (a, b)]
    | UCOMISS (a, b) ->
      let* a, ai = op a in
      let+ b, bi = op b in
      ai @ bi @ [UCOMISS (a, b)]
    | UD2 -> !![i]
    | XOR (a, b) ->
      let* a, ai = op a in
      let+ b, bi = op b in
      ai @ bi @ [XOR (a, b)]
    | XORPD (a, b) ->
      let* a, ai = op a in
      let+ b, bi = op b in
      ai @ bi @ [XORPD (a, b)]
    | XORPS (a, b) ->
      let* a, ai = op a in
      let+ b, bi = op b in
      ai @ bi @ [XORPS (a, b)]
    | MOV_ (a, b) ->
      let* a, ai = op a in
      let+ b, bi = op b in
      ai @ bi @ [MOV_ (a, b)]
    | JMPtbl _ -> !![i]
end

module Assign_slots = struct
  let find offsets rv = match Regvar.which rv with
    | Second (v, _) -> Map.find offsets v
    | First _ -> None

  (* XXX: fix this to account for overflow *)
  let add_disp off = function
    | Dsym (s, o) -> Dsym (s, o + off)
    | Dimm i -> Dimm Int32.(i + of_int_exn off)
    | Dlbl _ -> assert false

  let idisp i = Dimm (Int32.of_int_exn i)

  let assign_amode base offsets a = match a with
    | Ad _d -> a
    | Ab b ->
      begin match find offsets b with
        | Some 0 -> Ab base
        | Some o -> Abd (base, idisp o)
        | None -> a
      end
    | Abd (b, d) ->
      begin match find offsets b with
        | Some o -> Abd (base, add_disp o d)
        | None -> a
      end
    | Abis (b, i, s) ->
      begin match find offsets b, find offsets i with
        | None, None -> a
        | Some 0, None -> Abis (base, i, s)
        | Some o, None -> Abisd (base, i, s, idisp o)
        | _, Some _ -> assert false
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
        | _, Some _ -> assert false
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

let no_frame_prologue regs size =
  let size = Int64.of_int @@ align8 @@ max size 8 in
  let rsp = Oreg (Regvar.reg `rsp, `i64) in
  List.concat [
    List.map regs ~f:(fun r ->
        PUSH (Oreg (Regvar.reg r, `i64)));
    [SUB (rsp, Oimm (size, `i64))]
  ]

let no_frame_epilogue regs size =
  let size = Int64.of_int @@ align8 @@ max size 8 in
  let rsp = Oreg (Regvar.reg `rsp, `i64) in
  List.concat [
    [ADD (rsp, Oimm (size, `i64))];
    List.rev regs |> List.map ~f:(fun r ->
          POP (Oreg (Regvar.reg r, `i64)));
  ]

let frame_prologue regs size =
  let size = Int64.of_int @@ align8 size in
  let rsp = Oreg (Regvar.reg `rsp, `i64) in
  let rbp = Oreg (Regvar.reg `rbp, `i64) in
  List.concat [
    (* Push the frame pointer and give it the base of the stack. *)
    [PUSH rbp;
     MOV (rbp, rsp)];
    (* Allocate space. *)
    (if Int64.(size = 0L) then []
     else [SUB (rsp, Oimm (size, `i64))]);
    (* Push the callee-save registers. *)
    List.map regs ~f:(fun r ->
        PUSH (Oreg (Regvar.reg r, `i64)));
  ]

let frame_epilogue regs size =
  let size = Int64.of_int @@ align8 size in
  let rsp = Oreg (Regvar.reg `rsp, `i64) in
  let rbp = Oreg (Regvar.reg `rbp, `i64) in
  List.concat [
    (* Pop the callee-save registers in reverse order. *)
    List.rev regs |> List.map ~f:(fun r ->
        POP (Oreg (Regvar.reg r, `i64)));
    (* Deallocate space. *)
    (if Int64.(size = 0L) then []
     else [ADD (rsp, Oimm (size, `i64))]);
    (* Pop the frame pointer. *)
    [POP rbp];
  ]
