(* Helpers required by [Regalloc]. *)

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

let load_from_slot ~dst ~src =
  (* FIXME: we need the types *)
  match classof dst with
  | `gpr -> MOV (Oreg (dst, `i64), Omem (Ab src, `i64))
  | `fp -> MOVSD (Oreg (dst, `f64), Omem (Ab src, `i64))

let store_to_slot ~src ~dst =
  (* FIXME: we need the types *)
  match classof src with
  | `gpr -> MOV (Omem (Ab dst, `i64), Oreg (src, `i64))
  | `fp -> MOVSD (Omem (Ab dst, `i64), Oreg (src, `f64))

let substitute_amode f = function
  | Ad _ as a -> a
  | Ab b -> Ab (f b)
  | Abi (b, i) -> Abi (f b, f i)
  | Abd (b, d) -> Abd (f b, d)
  | Abid (b, i, d) -> Abid (f b, f i, d)
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
