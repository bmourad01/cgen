open Core

let word : Type.imm_base = `i64

module Reg = struct
  type gpr = [
    | `rax
    | `rcx
    | `rdx
    | `rbx
    | `rsi
    | `rdi
    | `rsp
    | `rbp
    | `r8
    | `r9
    | `r10
    | `r11
    | `r12
    | `r13
    | `r14
    | `r15
  ] [@@deriving compare, equal, sexp]

  let pp_gpr8 ppf : gpr -> unit = function
    | `rax -> Format.fprintf ppf "al"
    | `rcx -> Format.fprintf ppf "cl"
    | `rdx -> Format.fprintf ppf "dl"
    | `rbx -> Format.fprintf ppf "bl"
    | `rsi -> Format.fprintf ppf "sil"
    | `rdi -> Format.fprintf ppf "dil"
    | `rsp -> Format.fprintf ppf "spl"
    | `rbp -> Format.fprintf ppf "bpl"
    | `r8  -> Format.fprintf ppf "r8b"
    | `r9  -> Format.fprintf ppf "r9b"
    | `r10 -> Format.fprintf ppf "r10b"
    | `r11 -> Format.fprintf ppf "r11b"
    | `r12 -> Format.fprintf ppf "r12b"
    | `r13 -> Format.fprintf ppf "r13b"
    | `r14 -> Format.fprintf ppf "r14b"
    | `r15 -> Format.fprintf ppf "r15b"

  let pp_gpr16 ppf : gpr -> unit = function
    | `rax -> Format.fprintf ppf "ax"
    | `rcx -> Format.fprintf ppf "cx"
    | `rdx -> Format.fprintf ppf "dx"
    | `rbx -> Format.fprintf ppf "bx"
    | `rsi -> Format.fprintf ppf "si"
    | `rdi -> Format.fprintf ppf "di"
    | `rsp -> Format.fprintf ppf "sp"
    | `rbp -> Format.fprintf ppf "bp"
    | `r8  -> Format.fprintf ppf "r8w"
    | `r9  -> Format.fprintf ppf "r9w"
    | `r10 -> Format.fprintf ppf "r10w"
    | `r11 -> Format.fprintf ppf "r11w"
    | `r12 -> Format.fprintf ppf "r12w"
    | `r13 -> Format.fprintf ppf "r13w"
    | `r14 -> Format.fprintf ppf "r14w"
    | `r15 -> Format.fprintf ppf "r15w"

  let pp_gpr32 ppf : gpr -> unit = function
    | `rax -> Format.fprintf ppf "eax"
    | `rcx -> Format.fprintf ppf "ecx"
    | `rdx -> Format.fprintf ppf "edx"
    | `rbx -> Format.fprintf ppf "ebx"
    | `rsi -> Format.fprintf ppf "esi"
    | `rdi -> Format.fprintf ppf "edi"
    | `rsp -> Format.fprintf ppf "esp"
    | `rbp -> Format.fprintf ppf "ebp"
    | `r8  -> Format.fprintf ppf "r8d"
    | `r9  -> Format.fprintf ppf "r9d"
    | `r10 -> Format.fprintf ppf "r10d"
    | `r11 -> Format.fprintf ppf "r11d"
    | `r12 -> Format.fprintf ppf "r12d"
    | `r13 -> Format.fprintf ppf "r13d"
    | `r14 -> Format.fprintf ppf "r14d"
    | `r15 -> Format.fprintf ppf "r15d"

  let pp_gpr ppf gpr =
    Format.fprintf ppf "%a" Sexp.pp (sexp_of_gpr gpr)

  type sse = [
    | `xmm0
    | `xmm1
    | `xmm2
    | `xmm3
    | `xmm4
    | `xmm5
    | `xmm6
    | `xmm7
    | `xmm8
    | `xmm9
    | `xmm10
    | `xmm11
    | `xmm12
    | `xmm13
    | `xmm14
    | `xmm15
  ] [@@deriving compare, equal, sexp]

  let pp_sse ppf sse =
    Format.fprintf ppf "%a" Sexp.pp (sexp_of_sse sse)

  type t = [
    | gpr
    | sse
  ] [@@deriving compare, equal, sexp]

  let is_gpr = function
    | #gpr -> true
    | #sse -> false

  let is_sse = function
    | #gpr -> false
    | #sse -> true

  let pp ppf r =
    Format.fprintf ppf "%a" Sexp.pp (sexp_of_t r)

  let of_string s =
    Option.try_with @@ fun () -> t_of_sexp @@ Atom s

  let of_string_exn s = match of_string s with
    | None -> invalid_argf "%s is not a valid AMD64 register" s ()
    | Some r -> r
end

module Regvar = Regvar.Make(Reg)

module Insn = struct
  (* Displacements for addressing modes. *)
  type disp =
    | Dsym of string * int (* Symbol + offset *)
    | Dimm of int32        (* Immediate *)
  [@@deriving compare, equal, sexp]

  type rv = Regvar.t [@@deriving compare, equal, sexp]

  (* Memory addressing modes. Scale must be 1, 2, 4, or 8. *)
  type amode =
    | Ad    of disp                 (* Displacement *)
    | Ab    of rv                   (* Base *)
    | Abi   of rv * rv              (* Base + index *)
    | Abd   of rv * disp            (* Base + displacement *)
    | Abid  of rv * rv * disp       (* Base + index + displacement *)
    | Abis  of rv * rv * int        (* Base + index * scale *)
    | Aisd  of rv * int * disp      (* Index * scale + displacement *)
    | Abisd of rv * rv * int * disp (* Base + index * scale + displacement *)
  [@@deriving compare, equal, sexp]

  (* An argument to an instruction. *)
  type operand =
    | Oreg of rv * Type.basic (* Register *)
    | Oimm of int64           (* Immediate *)
    | Osym of string * int    (* Symbol + offset *)
    | Omem of amode           (* Memory address *)
  [@@deriving compare, equal, sexp]

  (* Condition codes. *)
  type cc =
    | Ca  (* ~CF & ~ZF *)
    | Cae (* ~CF *)
    | Cb  (* CF *)
    | Cbe (* CF | ZF *)
    | Ce  (* ZF *)
    | Cne (* ~ZF *)
    | Cg  (* ~ZF & SF=OF *)
    | Cge (* SF=OF *)
    | Cl  (* SF<>OF *)
    | Cle (* ZF | SF<>OF *)
    | Cp  (* PF *)
    | Cnp (* ~PF *)
  [@@deriving compare, equal, sexp]

  type t =
    | ADD      of operand * operand
    | ADDSD    of operand * operand
    | ADDSS    of operand * operand
    | AND      of operand * operand
    | CALL     of operand
    | CDQ
    | CMOVcc   of cc * operand * operand
    | CMP      of operand * operand
    | CQO
    | CWD
    | CVTSD2SI of operand * operand
    | CVTSI2SD of operand * operand
    | CVTSI2SS of operand * operand
    | CVTSS2SI of operand * operand
    | DEC      of operand
    | DIV      of operand
    | DIVSD    of operand * operand
    | DIVSS    of operand * operand
    | IDIV     of operand
    | IMUL1    of operand
    | IMUL2    of operand * operand
    | IMUL3    of operand * operand * int32
    | INC      of operand
    | Jcc      of cc * Label.t
    | JMP      of operand
    | LEA      of operand * operand
    | LZCNT    of operand * operand
    | MOV      of operand * operand
    | MOVD     of operand * operand
    | MOVQ     of operand * operand
    | MOVSD    of operand * operand
    | MOVSS    of operand * operand
    | MOVSX    of operand * operand
    | MOVSXD   of operand * operand
    | MOVZX    of operand * operand
    | MUL      of operand
    | MULSD    of operand * operand
    | MULSS    of operand * operand
    | NEG      of operand
    | NOT      of operand
    | OR       of operand * operand
    | POP      of operand
    | POPCNT   of operand * operand
    | PUSH     of operand
    | RET
    | ROL      of operand * operand
    | ROR      of operand * operand
    | SAR      of operand * operand
    | SETcc    of cc * operand
    | SHL      of operand * operand
    | SHR      of operand * operand
    | SUB      of operand * operand
    | SUBSD    of operand * operand
    | SUBSS    of operand * operand
    | TEST     of operand * operand
    | TZCNT    of operand * operand
    | UCOMISD  of operand * operand
    | UCOMISS  of operand * operand
    | XOR      of operand * operand
    | XORPD    of operand * operand
    | XORPS    of operand * operand
  [@@deriving compare, equal, sexp]

  (* Helper for registers mentioned in an addressing mode. *)
  let rv_of_amode = function
    | Ab a -> [a]
    | Abi (a, b) ->  [a; b]
    | Abd (a, _) -> [a]
    | Abid (a, b, _) -> [a; b]
    | Aisd (a, _, _) -> [a]
    | Abisd (a, b, _, _) -> [a; b]
    | _ -> []

  (* All registers mentioned in operands. *)
  let rset operands =
    Set.of_list (module Regvar) @@
    List.bind operands ~f:(function
        | Oreg (a, _) -> [a]
        | Omem a -> rv_of_amode a
        | _ -> [])

  (* Only explicit register operands. *)
  let rset_reg operands =
    Set.of_list (module Regvar) @@
    List.bind operands ~f:(function
        | Oreg (a, _) -> [a]
        | _ -> [])

  (* Only registers mentioned in memory operands. *)
  let rset_mem operands =
    Set.of_list (module Regvar) @@
    List.bind operands ~f:(function
        | Omem a -> rv_of_amode a
        | _ -> [])

  (* Hardcoded registers. *)
  let rset' regs =
    Set.of_list (module Regvar) @@
    List.map regs ~f:(fun r -> Regvar.Reg r)

  (* Registers read by an instruction. *)
  let reads = function
    | ADD (a, b)
    | ADDSD (a, b)
    | ADDSS (a, b)
    | AND (a, b)
    | CMP (a, b)
    | DIVSD (a, b)
    | DIVSS (a, b)
    | IMUL2 (a, b)
    | MULSD (a, b)
    | MULSS (a, b)
    | OR (a, b)
    | ROL (a, b)
    | ROR (a, b)
    | SAR (a, b)
    | SHL (a, b)
    | SHR (a, b)
    | SUB (a, b)
    | SUBSD (a, b)
    | SUBSS (a, b)
    | TEST (a, b)
    | UCOMISD (a, b)
    | UCOMISS (a, b)
    | XOR (a, b)
    | XORPD (a, b)
    | XORPS (a, b)
      -> rset [a; b]
    | CALL a
    | PUSH a
      -> Set.union (rset' [`rsp]) (rset_mem [a])
    | CMOVcc (_, _, a)
    | CVTSD2SI (_, a)
    | CVTSI2SD (_, a)
    | CVTSI2SS (_, a)
    | CVTSS2SI (_, a)
    | DEC a
    | IMUL3 (_, a, _)
    | INC a
    | JMP a
    | LEA (_, a)
    | LZCNT (_, a)
    | MOV (_, a)
    | MOVD (_, a)
    | MOVQ (_, a)
    | MOVSD (_, a)
    | MOVSS (_, a)
    | MOVSX (_, a)
    | MOVSXD (_, a)
    | MOVZX (_, a)
    | NEG a
    | NOT a
    | POPCNT (_, a)
    | TZCNT (_, a)
      -> rset [a]
    | CDQ
    | CQO
    | CWD
      -> rset' [`rax]
    | DIV (Oreg (_, `i8) as a)
    | IDIV (Oreg (_, `i8) as a)
    | IMUL1 a
    | MUL a
      -> Set.union (rset' [`rax]) (rset [a])
    | DIV a
    | IDIV a
      -> Set.union (rset' [`rax; `rdx]) (rset [a])
    | Jcc (_, _)
    | SETcc (_, _)
      -> Set.empty (module Regvar)
    | POP a
      -> Set.union (rset' [`rsp]) (rset_mem [a])
    | RET
      -> rset' [`rsp]

  (* Registers written to by an instruction. *)
  let writes = function
    | ADD (a, _)
    | ADDSD (a, _)
    | ADDSS (a, _)
    | AND (a, _)
    | CMOVcc (_, a, _)
    | CVTSD2SI (a, _)
    | CVTSI2SD (a, _)
    | CVTSI2SS (a, _)
    | CVTSS2SI (a, _)
    | DEC a
    | DIVSD (a, _)
    | DIVSS (a, _)
    | IMUL2 (a, _)
    | IMUL3 (a, _, _)
    | INC a
    | LEA (a, _)
    | LZCNT (a, _)
    | MOV (a, _)
    | MOVD (a, _)
    | MOVQ (a, _)
    | MOVSD (a, _)
    | MOVSS (a, _)
    | MOVSX (a, _)
    | MOVSXD (a, _)
    | MOVZX (a, _)
    | MULSD (a, _)
    | MULSS (a, _)
    | NEG a
    | NOT a
    | OR (a, _)
    | POPCNT (a, _)
    | ROL (a, _)
    | ROR (a, _)
    | SAR (a, _)
    | SETcc (_, a)
    | SHL (a, _)
    | SHR (a, _)
    | SUB (a, _)
    | SUBSD (a, _)
    | SUBSS (a, _)
    | TZCNT (a, _)
    | XOR (a, _)
    | XORPD (a, _)
    | XORPS (a, _)
      -> rset_reg [a]
    | CALL _
    | PUSH _
    | RET
      -> rset' [`rsp]
    | CMP _
    | Jcc _
    | JMP _
    | TEST _
    | UCOMISD _
    | UCOMISS _
      -> Set.empty (module Regvar)
    (* Special case for 8-bit div/mul. *)
    | DIV Oreg (_, `i8)
    | IDIV Oreg (_, `i8)
    | IMUL1 Oreg (_, `i8)
    | MUL Oreg (_, `i8)
      -> rset' [`rax]
    | CDQ
    | CQO
    | CWD
    | DIV _
    | IDIV _
    | IMUL1 _
    | MUL _
      -> rset' [`rax; `rdx]
    | POP a
      -> Set.union (rset' [`rsp]) (rset_reg [a])
end
