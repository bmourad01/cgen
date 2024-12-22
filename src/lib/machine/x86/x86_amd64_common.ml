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
    | `rip
  ] [@@deriving compare, equal, sexp]

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
    try Some (t_of_sexp @@ Atom s)
    with _ -> None

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
  type arg = [
    | `arg of rv * Type.basic (* Register *)
    | `imm of int64           (* Immediate *)
    | `sym of string * int    (* Symbol + offset *)
    | `mem of amode           (* Memory address *)
  ] [@@deriving compare, equal, sexp]

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
    | ADD      of arg * arg
    | ADDSD    of arg * arg
    | ADDSS    of arg * arg
    | AND      of arg * arg
    | CALL     of arg
    | CDQ
    | CMOV     of cc * arg * arg
    | CMP      of arg * arg
    | CQO
    | CWD
    | CVTSD2SI of arg * arg
    | CVTSI2SD of arg * arg
    | CVTSI2SS of arg * arg
    | CVTSS2SI of arg * arg
    | DEC      of arg
    | DIV      of arg
    | DIVSD    of arg * arg
    | DIVSS    of arg * arg
    | IDIV     of arg
    | IMUL1    of arg
    | IMUL2    of arg * arg
    | IMUL3    of arg * arg * int32
    | INC      of arg
    | JCC      of cc * Label.t
    | JMP      of arg
    | LEA      of arg * arg
    | LZCNT    of arg * arg
    | MOV      of arg * arg
    | MOVD     of arg * arg
    | MOVQ     of arg * arg
    | MOVSD    of arg * arg
    | MOVSS    of arg * arg
    | MOVSX    of arg * arg
    | MOVSXD   of arg * arg
    | MOVZX    of arg * arg
    | MUL      of arg
    | MULSD    of arg * arg
    | MULSS    of arg * arg
    | NEG      of arg
    | NOT      of arg
    | OR       of arg * arg
    | POP      of arg
    | POPCNT   of arg * arg
    | PUSH     of arg
    | RET
    | ROL      of arg * arg
    | ROR      of arg * arg
    | SAR      of arg * arg
    | SETCC    of cc * arg
    | SHL      of arg * arg
    | SHR      of arg * arg
    | SUB      of arg * arg
    | SUBSD    of arg * arg
    | SUBSS    of arg * arg
    | TEST     of arg * arg
    | TZCNT    of arg * arg
    | UCOMISD  of arg * arg
    | UCOMISS  of arg * arg
    | XOR      of arg * arg
    | XORPD    of arg * arg
    | XORPS    of arg * arg
  [@@deriving compare, equal, sexp]

  let reads i =
    let r args =
      Set.of_list (module Regvar) @@
      List.filter_map args ~f:(function
          | `arg (a, _) -> Some a
          | _ -> None) in
    let rl regs =
      Set.of_list (module Regvar) @@
      List.map regs ~f:(fun r -> Regvar.Reg r) in
    match i with
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
      -> r [a; b]
    | CALL a
    | CMOV (_, _, a)
    | CVTSD2SI (_, a)
    | CVTSI2SD (_, a)
    | CVTSI2SS (_, a)
    | CVTSS2SI (_, a)
    | DEC a
    | DIV a
    | IDIV a
    | IMUL1 a
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
    | MUL a
    | NEG a
    | NOT a
    | POPCNT (_, a)
    | PUSH a
    | TZCNT (_, a)
      -> r [a]
    | CDQ
    | CQO
    | CWD
      -> rl [`rax]
    | JCC (_, _)
    | POP _
    | RET
    | SETCC (_, _)
      -> Set.empty (module Regvar)

  let writes i =
    let r args =
      Set.of_list (module Regvar) @@
      List.filter_map args ~f:(function
          | `arg (a, _) -> Some a
          | _ -> None) in
    let rl regs =
      Set.of_list (module Regvar) @@
      List.map regs ~f:(fun r -> Regvar.Reg r) in
    match i with
    | ADD (a, _)
    | ADDSD (a, _)
    | ADDSS (a, _)
    | AND (a, _)
    | CMOV (_, a, _)
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
    | SETCC (_, a)
    | SHL (a, _)
    | SHR (a, _)
    | SUB (a, _)
    | SUBSD (a, _)
    | SUBSS (a, _)
    | TZCNT (a, _)
    | XOR (a, _)
    | XORPD (a, _)
    | XORPS (a, _)
      -> r [a]
    | CALL _
    | PUSH _
    | RET
      -> rl [`rsp]
    | CMP _
    | JCC _
    | JMP _
    | TEST _
    | UCOMISD _
    | UCOMISS _
      -> Set.empty (module Regvar)
    (* Special case for 8-bit div/mul. *)
    | DIV `arg (_, `i8)
    | IDIV `arg (_, `i8)
    | IMUL1 `arg (_, `i8)
    | MUL `arg (_, `i8)
      -> rl [`rax]
    | CDQ
    | CQO
    | CWD
    | DIV _
    | IDIV _
    | IMUL1 _
    | MUL _
      -> rl [`rax; `rdx]
    | POP a
      -> Set.union (rl [`rsp]) (r [a])
end
