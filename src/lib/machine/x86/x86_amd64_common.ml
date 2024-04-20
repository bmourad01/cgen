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
    try Some (t_of_sexp @@ Atom s)
    with _ -> None

  let of_string_exn s = match of_string s with
    | None -> invalid_argf "%s is not a valid AMD64 register" s ()
    | Some r -> r
end

module Insn = struct
  open X86_common

  type 'a add = [
    | `ADDrr64    of 'a * 'a
    | `ADDrm64    of 'a * 'a amode
    | `ADDmr64    of 'a amode * 'a
    | `ADDr64si8  of 'a * int
    | `ADDm64si8  of 'a amode * int
    | `ADDr64si32 of 'a * int32
    | `ADDm64si32 of 'a amode * int32
  ] [@@deriving compare, equal, sexp]

  type 'a and_ = [
    | `ANDrr64    of 'a * 'a
    | `ANDrm64    of 'a * 'a amode
    | `ANDmr64    of 'a amode * 'a
    | `ANDr64si8  of 'a * int
    | `ANDm64si8  of 'a amode * int
    | `ANDr64si32 of 'a * int32
    | `ANDm64si32 of 'a amode * int32
  ] [@@deriving compare, equal, sexp]

  (* CMOVP and CMOVNP are used for unordered and ordered
     floating point comparison, respectively. *)
  type 'a cmovcc = [
    | `CMOVArr64  of 'a * 'a (* ~CF & ~ZF *)
    | `CMOVArm64  of 'a * 'a amode
    | `CMOVAErr64 of 'a * 'a (* ~CF *)
    | `CMOVAErm64 of 'a * 'a amode
    | `CMOVBrr64  of 'a * 'a (* CF *)
    | `CMOVBrm64  of 'a * 'a amode
    | `CMOVBErr64 of 'a * 'a (* CF | ZF *)
    | `CMOVBErm64 of 'a * 'a amode
    | `CMOVErr64  of 'a * 'a (* ZF *)
    | `CMOVErm64  of 'a * 'a amode
    | `CMOVNErr64 of 'a * 'a (* ~ZF *)
    | `CMOVNErm64 of 'a * 'a amode
    | `CMOVGrr64  of 'a * 'a (* ~ZF & SF=OF *)
    | `CMOVGrm64  of 'a * 'a amode
    | `CMOVGErr64 of 'a * 'a (* SF=OF *)
    | `CMOVGErm64 of 'a * 'a amode
    | `CMOVLrr64  of 'a * 'a (* SF<>OF *)
    | `CMOVLrm64  of 'a * 'a amode
    | `CMOVLErr64 of 'a * 'a (* ZF | SF<>OF *)
    | `CMOVLErm64 of 'a * 'a amode
    | `CMOVPrr64  of 'a * 'a (* PF *)
    | `CMOVPrm64  of 'a * 'a amode
    | `CMOVNPrr64 of 'a * 'a (* ~PF *)
    | `CMOVNPrm64 of 'a * 'a amode
  ] [@@deriving compare, equal, sexp]

  type 'a cmp = [
    | `CMPrr64    of 'a * 'a
    | `CMPrm64    of 'a * 'a amode
    | `CMPmr64    of 'a amode * 'a
    | `CMPr64si32 of 'a * int32
    | `CMPm64si32 of 'a * int32
  ] [@@deriving compare, equal, sexp]

  type cqo = [
    | `CQO
  ] [@@deriving compare, equal, sexp]

  type 'a cvtsi2sd = [
    | `CVTSD2SIrr64 of 'a * 'a
    | `CVTSD2SIrm64 of 'a * 'a amode
  ] [@@deriving compare, equal, sexp]

  type 'a cvtsi2ss = [
    | `CVTSS2SIrr64 of 'a * 'a
    | `CVTSS2SIrm64 of 'a * 'a amode
  ] [@@deriving compare, equal, sexp]

  type 'a cvtsd2si = [
    | `CVTSD2SIr64r of 'a * 'a
    | `CVTSD2SIr64m of 'a * 'a amode
  ] [@@deriving compare, equal, sexp]

  type 'a cvtss2si = [
    | `CVTSS2SIr64r of 'a * 'a
    | `CVTSS2SIr64m of 'a * 'a amode
  ] [@@deriving compare, equal, sexp]

  type 'a dec = [
    | `DECr64 of 'a
    | `DECm64 of 'a amode
  ] [@@deriving compare, equal, sexp]

  type 'a div = [
    | `DIVr64 of 'a
    | `DIVm64 of 'a amode
  ] [@@deriving compare, equal, sexp]

  type 'a idiv = [
    | `IDIVr64 of 'a
    | `IDIVm64 of 'a amode
  ] [@@deriving compare, equal, sexp]

  type 'a imul = [
    | `IMULr64     of 'a
    | `IMULm64     of 'a amode
    | `IMULrr64    of 'a * 'a
    | `IMULrm64    of 'a * 'a amode
    | `IMULrr64si8 of 'a * 'a * int
    | `IMULrm64si8 of 'a * 'a amode * int
    | `IMULrr64i32 of 'a * 'a * int32
    | `IMULrm64i32 of 'a * 'a amode * int32
  ] [@@deriving compare, equal, sexp]

  type 'a inc = [
    | `INCr64 of 'a
    | `INCm64 of 'a amode
  ] [@@deriving compare, equal, sexp]

  type 'a lzcnt = [
    | `LZCNTrr64 of 'a * 'a
    | `LZCNTrm64 of 'a * 'a amode
  ] [@@deriving compare, equal, sexp]

  type 'a mov = [
    | `MOVrr64 of 'a * 'a
    | `MOVrm64 of 'a * 'a amode
    | `MOVmr64 of 'a amode * 'a
  ] [@@deriving compare, equal, sexp]

  type 'a movabs = [
    | `MOVABSri   of 'a * int64
    | `MOVABSr8o  of int64 (* AL is implied as the destination. *)
    | `MOVABSr16o of int64 (* AX is implied as the destination. *)
    | `MOVABSr32o of int64 (* EAX is implied as the destination. *)
    | `MOVABSr64o of int64 (* RAX is implied as the destination. *)
    | `MOVABSor8  of int64 (* AL is implied as the source. *)
    | `MOVABSor16 of int64 (* AX is implied as the source. *)
    | `MOVABSor32 of int64 (* EAX is implied as the source. *)
    | `MOVABSor64 of int64 (* RAX is implied as the source. *)
  ] [@@deriving compare, equal, sexp]

  type 'a movq = [
    | `MOVQrr of 'a * 'a
    | `MOVQrm of 'a * 'a amode
    | `MOVQmr of 'a amode * 'a
  ] [@@deriving compare, equal, sexp]

  type 'a movzx = [
    | `MOVZXr64r8  of 'a * 'a
    | `MOVZXr64m8  of 'a * 'a amode
    | `MOVZXr64r16 of 'a * 'a
    | `MOVZXr64m16 of 'a * 'a amode
  ] [@@deriving compare, equal, sexp]

  type 'a mul = [
    | `MULr64 of 'a
    | `MULm64 of 'a amode
  ] [@@deriving compare, equal, sexp]

  type 'a neg = [
    | `NEGr64 of 'a
    | `NEGm64 of 'a amode
  ] [@@deriving compare, equal, sexp]

  type 'a not_ = [
    | `NOTr64 of 'a
    | `NOTm64 of 'a amode
  ] [@@deriving compare, equal, sexp]

  type 'a or_ = [
    | `ORrr64    of 'a * 'a
    | `ORrm64    of 'a * 'a amode
    | `ORmr64    of 'a amode * 'a
    | `ORr64si8  of 'a * int
    | `ORm64si8  of 'a amode * int
    | `ORr64si32 of 'a * int32
    | `ORm64si32 of 'a amode * int32
  ] [@@deriving compare, equal, sexp]

  type 'a pop = [
    | `POPr64 of 'a
    | `POPm64 of 'a amode
  ] [@@deriving compare, equal, sexp]

  type 'a popcnt = [
    | `POPCNTrr64 of 'a * 'a
    | `POPCNTrm64 of 'a * 'a amode
  ] [@@deriving compare, equal, sexp]

  type 'a push = [
    | `PUSHr64 of 'a
    | `PUSHm64 of 'a amode
  ] [@@deriving compare, equal, sexp]

  type 'a rol = [
    | `ROLr64  of 'a
    | `ROLm64  of 'a
    | `ROLr64i of 'a * int
    | `ROLm64i of 'a * int
  ] [@@deriving compare, equal, sexp]

  type 'a ror = [
    | `RORr64  of 'a
    | `RORm64  of 'a
    | `RORLr64i of 'a * int
    | `RORm64i of 'a * int
  ] [@@deriving compare, equal, sexp]

  type 'a sar = [
    | `SARr64  of 'a
    | `SARm64  of 'a
    | `SARLr64i of 'a * int
    | `SARm64i of 'a * int
  ] [@@deriving compare, equal, sexp]

  type 'a shl = [
    | `SHLr64  of 'a
    | `SHLm64  of 'a
    | `SHLr64i of 'a * int
    | `SHLm64i of 'a * int
  ] [@@deriving compare, equal, sexp]

  type 'a shr = [
    | `SHRr64  of 'a
    | `SHRm64  of 'a
    | `SHRr64i of 'a * int
    | `SHRm64i of 'a * int
  ] [@@deriving compare, equal, sexp]

  type 'a sub = [
    | `SUBrr64    of 'a * 'a
    | `SUBrm64    of 'a * 'a amode
    | `SUBmr64    of 'a amode * 'a
    | `SUBr64si8  of 'a * int
    | `SUBm64si8  of 'a amode * int
    | `SUBr64si32 of 'a * int32
    | `SUBm64si32 of 'a amode * int32
  ] [@@deriving compare, equal, sexp]

  type 'a test = [
    | `TESTrr64    of 'a * 'a
    | `TESTrm64    of 'a * 'a amode
    | `TESTmr64    of 'a amode * 'a
    | `TESTr64si32 of 'a * int32
    | `TESTm64si32 of 'a * int32
  ] [@@deriving compare, equal, sexp]

  type 'a tzcnt = [
    | `TZCNTrr64 of 'a * 'a
    | `TZCNTrm64 of 'a * 'a amode
  ] [@@deriving compare, equal, sexp]

  type 'a xor = [
    | `XORrr64    of 'a * 'a
    | `XORrm64    of 'a * 'a amode
    | `XORmr64    of 'a amode * 'a
    | `XORr64si8  of 'a * int
    | `XORm64si8  of 'a amode * int
    | `XORr64si32 of 'a * int32
    | `XORm64si32 of 'a amode * int32
  ] [@@deriving compare, equal, sexp]

  type 'a t = [
    (* Base instructions. *)
    | 'a insn_base
    (* 64-bit extensions. *)
    | 'a add
    | 'a and_
    | 'a cmovcc
    | 'a cmp
    | cqo
    | 'a cvtsi2sd
    | 'a cvtsi2ss
    | 'a cvtsd2si
    | 'a cvtss2si
    | 'a dec
    | 'a div
    | 'a idiv
    | 'a imul
    | 'a inc
    | 'a lzcnt
    | 'a mov
    | 'a movabs
    | 'a movq
    | 'a movzx
    | 'a mul
    | 'a neg
    | 'a not_
    | 'a or_
    | 'a pop
    | 'a popcnt
    | 'a push
    | 'a rol
    | 'a ror
    | 'a sar
    | 'a shl
    | 'a shr
    | 'a sub
    | 'a test
    | 'a tzcnt
    | 'a xor
  ] [@@deriving compare, equal, sexp]
end
