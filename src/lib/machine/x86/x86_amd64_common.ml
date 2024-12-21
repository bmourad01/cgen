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

module Insn = struct
  (* Displacements for addressing modes. *)
  type disp =
    | Dsym of string * int (* Symbol + offset *)
    | Dimm of int32        (* Immediate *)
  [@@deriving compare, equal, sexp]

  (* Memory addressing modes. Scale must be 1, 2, 4, or 8. *)
  type 'a amode =
    | Ad    of disp                 (* Displacement *)
    | Ab    of 'a                   (* Base *)
    | Abi   of 'a * 'a              (* Base + index *)
    | Abd   of 'a * disp            (* Base + displacement *)
    | Abid  of 'a * 'a * disp       (* Base + index + displacement *)
    | Abis  of 'a * 'a * int        (* Base + index * scale *)
    | Aisd  of 'a * int * disp      (* Index * scale + displacement *)
    | Abisd of 'a * 'a * int * disp (* Base + index * scale + displacement *)
  [@@deriving compare, equal, sexp]

  (* An argument to an instruction. *)
  type 'a arg = [
    | `reg of 'a * Type.basic (* Register *)
    | `imm of int64           (* Immediate *)
    | `sym of string * int    (* Symbol + offset *)
    | `mem of 'a amode        (* Memory address *)
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

  type 'a t =
    | ADD      of 'a arg * 'a arg
    | ADDSD    of 'a arg * 'a arg
    | ADDSS    of 'a arg * 'a arg
    | AND      of 'a arg * 'a arg
    | CALL     of 'a arg
    | CDQ
    | CMOV     of cc * 'a arg * 'a arg
    | CMP      of 'a arg * 'a arg
    | CQO
    | CWD
    | CVTSD2SI of 'a arg * 'a arg
    | CVTSI2SD of 'a arg * 'a arg
    | CVTSI2SS of 'a arg * 'a arg
    | CVTSS2SI of 'a arg * 'a arg
    | DEC      of 'a arg
    | DIV      of 'a arg
    | DIVSD    of 'a arg * 'a arg
    | DIVSS    of 'a arg * 'a arg
    | IDIV     of 'a arg
    | IMUL1    of 'a arg
    | IMUL2    of 'a arg * 'a arg
    | IMUL3    of 'a arg * 'a arg * int32
    | INC      of 'a arg
    | JCC      of cc * Label.t
    | JMP      of 'a arg
    | LEA      of 'a arg * 'a arg
    | LZCNT    of 'a arg * 'a arg
    | MOV      of 'a arg * 'a arg
    | MOVD     of 'a arg * 'a arg
    | MOVQ     of 'a arg * 'a arg
    | MOVSD    of 'a arg * 'a arg
    | MOVSS    of 'a arg * 'a arg
    | MOVSX    of 'a arg * 'a arg
    | MOVSXD   of 'a arg * 'a arg
    | MOVZX    of 'a arg * 'a arg
    | MUL      of 'a arg
    | MULSD    of 'a arg * 'a arg
    | MULSS    of 'a arg * 'a arg
    | NEG      of 'a arg
    | NOT      of 'a arg
    | OR       of 'a arg
    | POP      of 'a arg
    | POPCNT   of 'a arg
    | PUSH     of 'a arg
    | RET
    | ROL      of 'a arg * 'a arg
    | ROR      of 'a arg * 'a arg
    | SAR      of 'a arg * 'a arg
    | SETCC    of cc * 'a arg
    | SHL      of 'a arg * 'a arg
    | SHR      of 'a arg * 'a arg
    | SUB      of 'a arg * 'a arg
    | SUBSD    of 'a arg * 'a arg
    | SUBSS    of 'a arg * 'a arg
    | TEST     of 'a arg * 'a arg
    | TZCNT    of 'a arg * 'a arg
    | UCOMISD  of 'a arg * 'a arg
    | UCOMISS  of 'a arg * 'a arg
    | XOR      of 'a arg * 'a arg
    | XORPD    of 'a arg * 'a arg
    | XORPS    of 'a arg * 'a arg
  [@@deriving compare, equal, sexp]
end
