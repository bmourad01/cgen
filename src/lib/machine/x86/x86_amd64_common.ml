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
  ] [@@deriving bin_io, compare, equal, sexp]

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
  ] [@@deriving bin_io, compare, equal, sexp]

  let pp_sse ppf sse =
    Format.fprintf ppf "%a" Sexp.pp (sexp_of_sse sse)

  type t = [
    | gpr
    | sse
    | `rip
  ] [@@deriving bin_io, compare, equal, sexp]

  let is_gpr = function
    | #gpr -> true
    | #sse -> false
    | `rip -> false

  let is_sse = function
    | #gpr -> false
    | #sse -> true
    | `rip -> false

  let is_rip = function
    | `rip -> true
    | _ -> false

  let pp ppf r =
    Format.fprintf ppf "%a" Sexp.pp (sexp_of_t r)

  let of_string s =
    Option.try_with @@ fun () -> t_of_sexp @@ Atom s

  let of_string_exn s = match of_string s with
    | None -> invalid_argf "%s is not a valid AMD64 register" s ()
    | Some r -> r
end

module Regvar = Machine_regvar.Make(Reg)

type rv = Regvar.t [@@deriving bin_io, compare, equal, sexp]

module Insn = struct
  (* Displacements for addressing modes. *)
  type disp =
    | Dsym of string * int (* Symbol + offset *)
    | Dimm of int32        (* Immediate *)
  [@@deriving bin_io, compare, equal, sexp]

  let pp_disp ppf = function
    | Dsym (s, o) when o < 0 ->
      Format.fprintf ppf "$%s-%d" s (-o)
    | Dsym (s, o) when o > 0 ->
      Format.fprintf ppf "$%s+%d" s o
    | Dsym (s, _) ->
      Format.fprintf ppf "$%s" s
    | Dimm i ->
      Format.fprintf ppf "0x%lx" i

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
  [@@deriving bin_io, compare, equal, sexp]

  let pp_amode ppf = function
    | Ad d ->
      Format.fprintf ppf "%a" pp_disp d
    | Ab b ->
      Format.fprintf ppf "%a" Regvar.pp b
    | Abi (b, i) ->
      Format.fprintf ppf "%a + %a"
        Regvar.pp b Regvar.pp i
    | Abd (b, d) ->
      Format.fprintf ppf "%a + %a"
        Regvar.pp b pp_disp d
    | Abid (b, i, d) ->
      Format.fprintf ppf "%a + %a*1 + %a"
        Regvar.pp b Regvar.pp i pp_disp d
    | Abis (b, i, s) ->
      Format.fprintf ppf "%a + %a*%d"
        Regvar.pp b Regvar.pp i s
    | Aisd (i, s, d) ->
      Format.fprintf ppf "%a*%d + %a"
        Regvar.pp i s pp_disp d
    | Abisd (b, i, s, d) ->
      Format.fprintf ppf "%a + %a*%d + %a"
        Regvar.pp b Regvar.pp i s pp_disp d

  (* An argument to an instruction. *)
  type operand =
    | Oreg of rv * Type.basic (* Register *)
    | Oimm of int64           (* Immediate *)
    | Osym of string * int    (* Symbol + offset *)
    | Omem of amode           (* Memory address *)
  [@@deriving bin_io, compare, equal, sexp]

  let pp_operand ppf = function
    (* Print the correct register syntax based on the type. *)
    | Oreg (Reg (#Reg.sse as r), #Type.fp) ->
      Format.fprintf ppf "%a" Reg.pp_sse r
    | Oreg (Reg (#Reg.gpr as r), `i8) ->
      Format.fprintf ppf "%a" Reg.pp_gpr8 r
    | Oreg (Reg (#Reg.gpr as r), `i16) ->
      Format.fprintf ppf "%a" Reg.pp_gpr16 r
    | Oreg (Reg (#Reg.gpr as r), `i32) ->
      Format.fprintf ppf "%a" Reg.pp_gpr32 r
    | Oreg (Reg (#Reg.gpr as r), `i64) ->
      Format.fprintf ppf "%a" Reg.pp_gpr r
    (* This should always be a variable in practice, but we
       won't enforce it here. *)
    | Oreg (r, t) ->
      Format.fprintf ppf "%a:%a" Regvar.pp r Type.pp_basic t
    | Oimm i ->
      Format.fprintf ppf "0x%Lx" i
    | Osym (s, o) when o < 0 ->
      Format.fprintf ppf "%s-%d" s (-o)
    | Osym (s, o) when o > 0 ->
      Format.fprintf ppf "%s+%d" s o
    | Osym (s, _) ->
      Format.fprintf ppf "%s" s
    | Omem a ->
      Format.fprintf ppf "[%a]" pp_amode a

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
  [@@deriving bin_io, compare, equal, sexp]

  let pp_cc ppf = function
    | Ca  -> Format.fprintf ppf "a"
    | Cae -> Format.fprintf ppf "ae"
    | Cb  -> Format.fprintf ppf "b"
    | Cbe -> Format.fprintf ppf "be"
    | Ce  -> Format.fprintf ppf "e"
    | Cne -> Format.fprintf ppf "ne"
    | Cg  -> Format.fprintf ppf "g"
    | Cge -> Format.fprintf ppf "ge"
    | Cl  -> Format.fprintf ppf "l"
    | Cle -> Format.fprintf ppf "le"
    | Cp  -> Format.fprintf ppf "p"
    | Cnp -> Format.fprintf ppf "np"

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
    | JMP      of [`op of operand | `lbl of Label.t]
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
  [@@deriving bin_io, compare, equal, sexp]

  let pp ppf i =
    let unary m a =
      Format.fprintf ppf "%s %a" m pp_operand a in
    let binary m a b =
      Format.fprintf ppf "%s %a, %a" m pp_operand a pp_operand b in
    match i with
    | ADD (a, b) -> binary "add" a b
    | ADDSD (a, b) -> binary "addsd" a b
    | ADDSS (a, b) -> binary "addss" a b
    | AND (a, b) -> binary "and" a b
    | CALL a -> unary "call" a
    | CDQ -> Format.fprintf ppf "cdq"
    | CMOVcc (cc, a, b) ->
      Format.fprintf ppf "cmov%a %a, %a"
        pp_cc cc pp_operand a pp_operand b
    | CMP (a, b) -> binary "cmp" a b
    | CQO -> Format.fprintf ppf "cqo"
    | CWD -> Format.fprintf ppf "cwd"
    | CVTSD2SI (a, b) -> binary "cvtsd2si" a b
    | CVTSI2SD (a, b) -> binary "cvtsi2sd" a b
    | CVTSI2SS (a, b) -> binary "cvtsi2ss" a b
    | CVTSS2SI (a, b) -> binary "cvtss2si" a b
    | DEC a -> unary "dec" a
    | DIV a -> unary "div" a
    | DIVSD (a, b) -> binary "divsd" a b
    | DIVSS (a, b) -> binary "divss" a b
    | IDIV a -> unary "idiv" a
    | IMUL1 a -> unary "imul" a
    | IMUL2 (a, b) -> binary "imul" a b
    | IMUL3 (a, b, c) ->
      Format.fprintf ppf "imul %a, %a, 0x%lx"
        pp_operand a pp_operand b c
    | INC a -> unary "inc" a
    | Jcc (cc, l) ->
      Format.fprintf ppf "j%a %a" pp_cc cc Label.pp l
    | JMP `op a -> unary "jmp" a
    | JMP `lbl l ->
      Format.fprintf ppf "jmp %a" Label.pp l
    | LEA (a, b) -> binary "lea" a b
    | LZCNT (a, b) -> binary "lzcnt" a b
    | MOV (a, b) -> binary "mov" a b
    | MOVD (a, b) -> binary "movd" a b
    | MOVQ (a, b) -> binary "movq" a b
    | MOVSD (a, b) -> binary "movsd" a b
    | MOVSS (a, b) -> binary "movss" a b
    | MOVSX (a, b) -> binary "movsx" a b
    | MOVSXD (a, b) -> binary "movsxd" a b
    | MOVZX (a, b) -> binary "movzx" a b
    | MUL a -> unary "mul" a
    | MULSD (a, b) -> binary "mulsd" a b
    | MULSS (a, b) -> binary "mulss" a b
    | NEG a -> unary "neg" a
    | NOT a -> unary "not" a
    | OR (a, b) -> binary "or" a b
    | POP a -> unary "pop" a
    | POPCNT (a, b) -> binary "popcnt" a b
    | PUSH a -> unary "push" a
    | RET -> Format.fprintf ppf "ret"
    | ROL (a, b) -> binary "rol" a b
    | ROR (a, b) -> binary "ror" a b
    | SAR (a, b) -> binary "sar" a b
    | SETcc (cc, a) ->
      Format.fprintf ppf "set%a %a" pp_cc cc pp_operand a
    | SHL (a, b) -> binary "shl" a b
    | SHR (a, b) -> binary "shr" a b
    | SUB (a, b) -> binary "sub" a b
    | SUBSD (a, b) -> binary "subsd" a b
    | SUBSS (a, b) -> binary "subss" a b
    | TEST (a, b) -> binary "test" a b
    | TZCNT (a, b) -> binary "tzcnt" a b
    | UCOMISD (a, b) -> binary "ucomisd" a b
    | UCOMISS (a, b) -> binary "ucomiss" a b
    | XOR (a, b) -> binary "xor" a b
    | XORPD (a, b) -> binary "xorpd" a b
    | XORPS (a, b) -> binary "xorps" a b

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
    Regvar.Set.of_list @@
    List.bind operands ~f:(function
        | Oreg (a, _) -> [a]
        | Omem a -> rv_of_amode a
        | _ -> [])

  (* Only explicit register operands. *)
  let rset_reg operands =
    Regvar.Set.of_list @@
    List.bind operands ~f:(function
        | Oreg (a, _) -> [a]
        | _ -> [])

  (* Only registers mentioned in memory operands. *)
  let rset_mem operands =
    Regvar.Set.of_list @@
    List.bind operands ~f:(function
        | Omem a -> rv_of_amode a
        | _ -> [])

  (* Hardcoded registers. *)
  let rset' regs =
    Regvar.Set.of_list @@
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
    | JMP `op a
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
    | JMP `lbl _
      -> Regvar.Set.empty
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
      -> Regvar.Set.empty
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
