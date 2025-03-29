(* Helpers required by the implementations in [Regalloc]. *)

open Core
open X86_amd64_common
open Insn

(* XXX: any more cases than this? *)
let copy = function
  | MOV (Oreg (d, _), Oreg (s, _))
  | MOVSS (Oreg (d, _), Oreg (s, _))
  | MOVSD (Oreg (d, _), Oreg (s, _)) -> Some (d, s)
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

let substitute i f =
  let op = substitute_operand f in
  match i with
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
