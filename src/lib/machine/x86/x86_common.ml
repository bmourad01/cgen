open Core

let little = true

type disp =
  | Dsym   of string * int
  | Dconst of int32
[@@deriving compare, equal, sexp]

type 'a amode =
  | Adisp               of disp
  | Abase               of 'a
  | Abaseindex          of 'a * 'a
  | Abasedisp           of 'a * disp
  | Abaseindexdisp      of 'a * 'a * disp
  | Abaseindexscale     of 'a * 'a * int
  | Aindexscaledisp     of 'a * int * disp
  | Abaseindexscaledisp of 'a * 'a * int * disp
[@@deriving compare, equal, sexp]

module Insn = struct
  type 'a add = [
    | `ADDri8    of 'a * int
    | `ADDri16   of 'a * int
    | `ADDri32   of 'a * int32
    | `ADDmi8    of 'a amode * int
    | `ADDmi16   of 'a amode * int
    | `ADDmi32   of 'a amode * int32
    | `ADDrr8    of 'a * 'a
    | `ADDrr16   of 'a * 'a
    | `ADDrr32   of 'a * 'a
    | `ADDrm8    of 'a * 'a amode
    | `ADDrm16   of 'a * 'a amode
    | `ADDrm32   of 'a * 'a amode
    | `ADDmr8    of 'a amode * 'a
    | `ADDmr16   of 'a amode * 'a
    | `ADDmr32   of 'a amode * 'a
    | `ADDr16si8 of 'a * int
    | `ADDr32si8 of 'a * int
    | `ADDm16si8 of 'a amode * int
    | `ADDm32si8 of 'a amode * int
  ] [@@deriving compare, equal, sexp]

  type 'a addsd = [
    | `ADDSDrr of 'a * 'a
    | `ADDSDrm of 'a * 'a amode
  ] [@@deriving compare, equal, sexp]

  type 'a addss = [
    | `ADDSSrr of 'a * 'a
    | `ADDSSrm of 'a * 'a amode
  ] [@@deriving compare, equal, sexp]

  type 'a and_ = [
    | `ANDri8    of 'a * int
    | `ANDri16   of 'a * int
    | `ANDri32   of 'a * int32
    | `ANDmi8    of 'a amode * int
    | `ANDmi16   of 'a amode * int
    | `ANDmi32   of 'a amode * int32
    | `ANDrr8    of 'a * 'a
    | `ANDrr16   of 'a * 'a
    | `ANDrr32   of 'a * 'a
    | `ANDrm8    of 'a * 'a amode
    | `ANDrm16   of 'a * 'a amode
    | `ANDrm32   of 'a * 'a amode
    | `ANDmr8    of 'a amode * 'a
    | `ANDmr16   of 'a amode * 'a
    | `ANDmr32   of 'a amode * 'a
    | `ANDr16si8 of 'a * int
    | `ANDr32si8 of 'a * int
    | `ANDm16si8 of 'a amode * int
    | `ANDm32si8 of 'a amode * int
  ] [@@deriving compare, equal, sexp]

  type 'a call = [
    | `CALL  of string * int (* symbol + offset *)
    | `CALLr of 'a
    | `CALLm of 'a amode
  ] [@@deriving compare, equal, sexp]

  type cdq = [
    | `CDQ
  ] [@@deriving compare, equal, sexp]

  (* CMOVP and CMOVNP are used for unordered and ordered
     floating point comparison, respectively. *)
  type 'a cmovcc = [
    | `CMOVArr16  of 'a * 'a (* ~CF & ~ZF *)
    | `CMOVArr32  of 'a * 'a
    | `CMOVArm16  of 'a * 'a amode
    | `CMOVArm32  of 'a * 'a amode
    | `CMOVAErr16 of 'a * 'a (* ~CF *)
    | `CMOVAErr32 of 'a * 'a
    | `CMOVAErm16 of 'a * 'a amode
    | `CMOVAErm32 of 'a * 'a amode
    | `CMOVBrr16  of 'a * 'a (* CF *)
    | `CMOVBrr32  of 'a * 'a
    | `CMOVBrm16  of 'a * 'a amode
    | `CMOVBrm32  of 'a * 'a amode
    | `CMOVBErr16 of 'a * 'a (* CF | ZF *)
    | `CMOVBErr32 of 'a * 'a
    | `CMOVBErm16 of 'a * 'a amode
    | `CMOVBErm32 of 'a * 'a amode
    | `CMOVErr16  of 'a * 'a (* ZF *)
    | `CMOVErr32  of 'a * 'a
    | `CMOVErm16  of 'a * 'a amode
    | `CMOVErm32  of 'a * 'a amode
    | `CMOVNErr16 of 'a * 'a (* ~ZF *)
    | `CMOVNErr32 of 'a * 'a
    | `CMOVNErm16 of 'a * 'a amode
    | `CMOVNErm32 of 'a * 'a amode
    | `CMOVGrr16  of 'a * 'a (* ~ZF & SF=OF *)
    | `CMOVGrr32  of 'a * 'a
    | `CMOVGrm16  of 'a * 'a amode
    | `CMOVGrm32  of 'a * 'a amode
    | `CMOVGErr16 of 'a * 'a (* SF=OF *)
    | `CMOVGErr32 of 'a * 'a
    | `CMOVGErm16 of 'a * 'a amode
    | `CMOVGErm32 of 'a * 'a amode
    | `CMOVLrr16  of 'a * 'a (* SF<>OF *)
    | `CMOVLrr32  of 'a * 'a
    | `CMOVLrm16  of 'a * 'a amode
    | `CMOVLrm32  of 'a * 'a amode
    | `CMOVLErr16 of 'a * 'a (* ZF | SF<>OF *)
    | `CMOVLErr32 of 'a * 'a
    | `CMOVLErm16 of 'a * 'a amode
    | `CMOVLErm32 of 'a * 'a amode
    | `CMOVPrr16  of 'a * 'a (* PF *)
    | `CMOVPrr32  of 'a * 'a
    | `CMOVPrm16  of 'a * 'a amode
    | `CMOVPrm32  of 'a * 'a amode
    | `CMOVNPrr16 of 'a * 'a (* ~PF *)
    | `CMOVNPrr32 of 'a * 'a
    | `CMOVNPrm16 of 'a * 'a amode
    | `CMOVNPrm32 of 'a * 'a amode
  ] [@@deriving compare, equal, sexp]

  type 'a cmp = [
    | `CMPri8  of 'a * int
    | `CMPri16 of 'a * int
    | `CMPri32 of 'a * int32
    | `CMPmi8  of 'a amode * int
    | `CMPmi16 of 'a amode * int
    | `CMPmi32 of 'a amode * int32
    | `CMPrr8  of 'a * 'a
    | `CMPrr16 of 'a * 'a
    | `CMPrr32 of 'a * 'a
    | `CMPrm8  of 'a * 'a amode
    | `CMPrm16 of 'a * 'a amode
    | `CMPrm32 of 'a * 'a amode
    | `CMPmr8  of 'a amode * 'a
    | `CMPmr16 of 'a amode * 'a
    | `CMPmr32 of 'a amode * 'a
  ] [@@deriving compare, equal, sexp]

  type cwd = [
    | `CWD
  ] [@@deriving compare, equal, sexp]

  type 'a cvtsi2sd = [
    | `CVTSD2SIrr32 of 'a * 'a
    | `CVTSD2SIrm32 of 'a * 'a amode
  ] [@@deriving compare, equal, sexp]

  type 'a cvtsi2ss = [
    | `CVTSS2SIrr32 of 'a * 'a
    | `CVTSS2SIrm32 of 'a * 'a amode
  ] [@@deriving compare, equal, sexp]

  type 'a cvtsd2si = [
    | `CVTSD2SIr32r of 'a * 'a
    | `CVTSD2SIr32m of 'a * 'a amode
  ] [@@deriving compare, equal, sexp]

  type 'a cvtss2si = [
    | `CVTSS2SIr32r of 'a * 'a
    | `CVTSS2SIr32m of 'a * 'a amode
  ] [@@deriving compare, equal, sexp]

  type 'a dec = [
    | `DECr8  of 'a
    | `DECr16 of 'a
    | `DECr32 of 'a
    | `DECm8  of 'a amode
    | `DECm16 of 'a amode
    | `DECm32 of 'a amode
  ] [@@deriving compare, equal, sexp]

  type 'a div = [
    | `DIVr8  of 'a
    | `DIVr16 of 'a
    | `DIVr32 of 'a
    | `DIVm8  of 'a amode
    | `DIVm16 of 'a amode
    | `DIVm32 of 'a amode
  ] [@@deriving compare, equal, sexp]

  type 'a divsd = [
    | `DIVSDrr of 'a * 'a
    | `DIVSDrm of 'a * 'a amode
  ] [@@deriving compare, equal, sexp]

  type 'a divss = [
    | `DIVSSrr of 'a * 'a
    | `DIVSSrm of 'a * 'a amode
  ] [@@deriving compare, equal, sexp]

  type 'a idiv = [
    | `IDIVr8  of 'a
    | `IDIVr16 of 'a
    | `IDIVr32 of 'a
    | `IDIVm8  of 'a amode
    | `IDIVm16 of 'a amode
    | `IDIVm32 of 'a amode
  ] [@@deriving compare, equal, sexp]

  type 'a imul = [
    | `IMULr8      of 'a
    | `IMULr16     of 'a
    | `IMULr32     of 'a
    | `IMULm8      of 'a amode
    | `IMULm16     of 'a amode
    | `IMULm32     of 'a amode
    | `IMULrr8     of 'a * 'a
    | `IMULrr16    of 'a * 'a
    | `IMULrr32    of 'a * 'a
    | `IMULrm8     of 'a * 'a amode
    | `IMULrm16    of 'a * 'a amode
    | `IMULrm32    of 'a * 'a amode
    | `IMULrr8si8  of 'a * 'a * int
    | `IMULrr16si8 of 'a * 'a * int
    | `IMULrr32si8 of 'a * 'a * int
    | `IMULrm8si8  of 'a * 'a amode * int
    | `IMULrm16si8 of 'a * 'a amode * int
    | `IMULrm32si8 of 'a * 'a amode * int
    | `IMULrri16   of 'a * 'a * int
    | `IMULrri32   of 'a * 'a * int32
    | `IMULrmi16   of 'a * 'a amode * int
    | `IMULrmi32   of 'a * 'a amode * int32
  ] [@@deriving compare, equal, sexp]

  type 'a inc = [
    | `INCr8  of 'a
    | `INCr16 of 'a
    | `INCr32 of 'a
    | `INCm8  of 'a amode
    | `INCm16 of 'a amode
    | `INCm32 of 'a amode
  ] [@@deriving compare, equal, sexp]

  (* JP and JNP are used for unordered and ordered
     floating point comparison, respectively. *)
  type 'a jcc = [
    | `JA  of Label.t (* ~CF & ~ZF *)
    | `JAE of Label.t (* ~CF *)
    | `JB  of Label.t (* CF *)
    | `JBE of Label.t (* CF | ZF *)
    | `JE  of Label.t (* ZF *)
    | `JNE of Label.t (* ~ZF *)
    | `JG  of Label.t (* ~ZF & SF=OF *)
    | `JGE of Label.t (* SF=OF *)
    | `JL  of Label.t (* SF<>OF *)
    | `JLE of Label.t (* ZF | SF<>OF *)
    | `JP  of Label.t (* PF *)
    | `JNP of Label.t (* ~PF *)
  ] [@@deriving compare, equal, sexp]

  type 'a jmp = [
    | `JMP  of Label.t
    | `JMPr of 'a
    | `JMPm of 'a amode
  ] [@@deriving compare, equal, sexp]

  type 'a lea = [
    | `LEA  of string * int (* symbol + offset *)
    | `LEAm of 'a amode
  ] [@@deriving compare, equal, sexp]

  type 'a lzcnt = [
    | `LZCNTrr16 of 'a * 'a
    | `LZCNTrr32 of 'a * 'a
    | `LZCNTrm16 of 'a * 'a amode
    | `LZCNTrm32 of 'a * 'a amode
  ] [@@deriving compare, equal, sexp]

  type 'a mov = [
    | `MOVri8  of 'a * int
    | `MOVri16 of 'a * int
    | `MOVri32 of 'a * int32
    | `MOVmi8  of 'a amode * int
    | `MOVmi16 of 'a amode * int
    | `MOVmi32 of 'a amode * int32
    | `MOVrr8  of 'a * 'a
    | `MOVrr16 of 'a * 'a
    | `MOVrr32 of 'a * 'a
    | `MOVrm8  of 'a * 'a amode
    | `MOVrm16 of 'a * 'a amode
    | `MOVrm32 of 'a * 'a amode
    | `MOVmr8  of 'a amode * 'a
    | `MOVmr16 of 'a amode * 'a
    | `MOVmr32 of 'a amode * 'a
  ] [@@deriving compare, equal, sexp]

  type 'a movd = [
    | `MOVDrr of 'a * 'a
    | `MOVDrm of 'a * 'a amode
    | `MOVDmr of 'a amode * 'a
  ] [@@deriving compare, equal, sexp]

  type 'a movsd = [
    | `MOVSDrr of 'a * 'a
    | `MOVSDrm of 'a * 'a amode
    | `MOVSDmr of 'a amode * 'a
  ] [@@deriving compare, equal, sexp]

  type 'a movss = [
    | `MOVSSrr of 'a * 'a
    | `MOVSSrm of 'a * 'a amode
    | `MOVSSmr of 'a amode * 'a
  ] [@@deriving compare, equal, sexp]

  type 'a movzx = [
    | `MOVZXr16r8  of 'a * 'a
    | `MOVZXr32r8  of 'a * 'a
    | `MOVZXr16m8  of 'a * 'a amode
    | `MOVZXr32m8  of 'a * 'a amode
    | `MOVZXr32r16 of 'a * 'a
    | `MOVZXr32m16 of 'a * 'a amode
  ] [@@deriving compare, equal, sexp]

  type 'a mul = [
    | `MULr8  of 'a
    | `MULr16 of 'a
    | `MULr32 of 'a
    | `MULm8  of 'a amode
    | `MULm16 of 'a amode
    | `MULm32 of 'a amode
  ] [@@deriving compare, equal, sexp]

  type 'a mulsd = [
    | `MULSDrr of 'a * 'a
    | `MULSDrm of 'a * 'a amode
  ] [@@deriving compare, equal, sexp]

  type 'a mulss = [
    | `MULSSrr of 'a * 'a
    | `MULSSrm of 'a * 'a amode
  ] [@@deriving compare, equal, sexp]

  type 'a neg = [
    | `NEGr8  of 'a
    | `NEGr16 of 'a
    | `NEGr32 of 'a
    | `NEGm8  of 'a amode
    | `NEGm16 of 'a amode
    | `NEGm32 of 'a amode
  ] [@@deriving compare, equal, sexp]

  type 'a not_ = [
    | `NOTr8  of 'a
    | `NOTr16 of 'a
    | `NOTr32 of 'a
    | `NOTm8  of 'a amode
    | `NOTm16 of 'a amode
    | `NOTm32 of 'a amode
  ] [@@deriving compare, equal, sexp]

  type 'a or_ = [
    | `ORri8    of 'a * int
    | `ORri16   of 'a * int
    | `ORri32   of 'a * int32
    | `ORmi8    of 'a amode * int
    | `ORmi16   of 'a amode * int
    | `ORmi32   of 'a amode * int32
    | `ORrr8    of 'a * 'a
    | `ORrr16   of 'a * 'a
    | `ORrr32   of 'a * 'a
    | `ORrm8    of 'a * 'a amode
    | `ORrm16   of 'a * 'a amode
    | `ORrm32   of 'a * 'a amode
    | `ORmr8    of 'a amode * 'a
    | `ORmr16   of 'a amode * 'a
    | `ORmr32   of 'a amode * 'a
    | `ORr16si8 of 'a * int
    | `ORr32si8 of 'a * int
    | `ORm16si8 of 'a amode * int
    | `ORm32si8 of 'a amode * int
  ] [@@deriving compare, equal, sexp]

  type 'a pop = [
    | `POPr8  of 'a
    | `POPr16 of 'a
    | `POPr32 of 'a
    | `POPm8  of 'a amode
    | `POPm16 of 'a amode
    | `POPm32 of 'a amode
  ] [@@deriving compare, equal, sexp]

  type 'a popcnt = [
    | `POPCNTrr16 of 'a * 'a
    | `POPCNTrr32 of 'a * 'a
    | `POPCNTrm16 of 'a * 'a amode
    | `POPCNTrm32 of 'a * 'a amode
  ] [@@deriving compare, equal, sexp]

  type 'a push = [
    | `PUSHi8  of int
    | `PUSHi16 of int
    | `PUSHi32 of int
    | `PUSHr8  of 'a
    | `PUSHr16 of 'a
    | `PUSHr32 of 'a
    | `PUSHm8  of 'a amode
    | `PUSHm16 of 'a amode
    | `PUSHm32 of 'a amode
  ] [@@deriving compare, equal, sexp]

  type 'a ret = [
    | `RET
  ] [@@deriving compare, equal, sexp]

  type 'a rol = [
    | `ROLr8  of 'a (* implicitly CL *)
    | `ROLr16 of 'a
    | `ROLr32 of 'a
    | `ROLm8  of 'a
    | `ROLm16 of 'a
    | `ROLm32 of 'a
    | `ROLr8i  of 'a * int
    | `ROLr16i of 'a * int
    | `ROLr32i of 'a * int
    | `ROLm8i  of 'a * int
    | `ROLm16i of 'a * int
    | `ROLm32i of 'a * int
  ] [@@deriving compare, equal, sexp]

  type 'a ror = [
    | `RORr8  of 'a (* implicitly CL *)
    | `RORr16 of 'a
    | `RORr32 of 'a
    | `RORm8  of 'a
    | `RORm16 of 'a
    | `RORm32 of 'a
    | `RORr8i  of 'a * int
    | `RORr16i of 'a * int
    | `RORr32i of 'a * int
    | `RORm8i  of 'a * int
    | `RORm16i of 'a * int
    | `RORm32i of 'a * int
  ] [@@deriving compare, equal, sexp]

  type 'a sar = [
    | `SARr8  of 'a (* implicitly CL *)
    | `SARr16 of 'a
    | `SARr32 of 'a
    | `SARm8  of 'a
    | `SARm16 of 'a
    | `SARm32 of 'a
    | `SARr8i  of 'a * int
    | `SARr16i of 'a * int
    | `SARr32i of 'a * int
    | `SARm8i  of 'a * int
    | `SARm16i of 'a * int
    | `SARm32i of 'a * int
  ] [@@deriving compare, equal, sexp]

  (* SETP and SETNP are used for unordered and ordered
     floating point comparison, respectively. *)
  type 'a setcc = [
    | `SETAr8  of 'a (* ~CF & ~ZF *)
    | `SETAm8  of 'a amode
    | `SETAEr8 of 'a (* ~CF *)
    | `SETAEm8 of 'a amode
    | `SETBr8  of 'a (* CF *)
    | `SETBm8  of 'a amode
    | `SETBEr8 of 'a (* CF | ZF *)
    | `SETBEm8 of 'a amode
    | `SETEr8  of 'a (* ZF *)
    | `SETEm8  of 'a amode
    | `SETNEr8 of 'a (* ~ZF *)
    | `SETNEm8 of 'a amode
    | `SETGr8  of 'a (* ~ZF & SF=OF *)
    | `SETGm8  of 'a amode
    | `SETGEr8 of 'a (* SF=OF *)
    | `SETGEm8 of 'a amode
    | `SETLr8  of 'a (* SF<>OF *)
    | `SETLm8  of 'a amode
    | `SETLEr8 of 'a (* ZF | SF<>OF *)
    | `SETLEm8 of 'a amode
    | `SETPr8  of 'a (* PF *)
    | `SETPm8  of 'a amode
    | `SETNPr8 of 'a (* ~PF *)
    | `SETNPm8 of 'a amode
  ] [@@deriving compare, equal, sexp]

  type 'a shl = [
    | `SHLr8  of 'a (* implicitly CL *)
    | `SHLr16 of 'a
    | `SHLr32 of 'a
    | `SHLm8  of 'a
    | `SHLm16 of 'a
    | `SHLm32 of 'a
    | `SHLr8i  of 'a * int
    | `SHLr16i of 'a * int
    | `SHLr32i of 'a * int
    | `SHLm8i  of 'a * int
    | `SHLm16i of 'a * int
    | `SHLm32i of 'a * int
  ] [@@deriving compare, equal, sexp]

  type 'a shr = [
    | `SHRr8  of 'a (* implicitly CL *)
    | `SHRr16 of 'a
    | `SHRr32 of 'a
    | `SHRm8  of 'a
    | `SHRm16 of 'a
    | `SHRm32 of 'a
    | `SHRr8i  of 'a * int
    | `SHRr16i of 'a * int
    | `SHRr32i of 'a * int
    | `SHRm8i  of 'a * int
    | `SHRm16i of 'a * int
    | `SHRm32i of 'a * int
  ] [@@deriving compare, equal, sexp]

  type 'a sub = [
    | `SUBri8    of 'a * int
    | `SUBri16   of 'a * int
    | `SUBri32   of 'a * int32
    | `SUBmi8    of 'a amode * int
    | `SUBmi16   of 'a amode * int
    | `SUBmi32   of 'a amode * int32
    | `SUBrr8    of 'a * 'a
    | `SUBrr16   of 'a * 'a
    | `SUBrr32   of 'a * 'a
    | `SUBrm8    of 'a * 'a amode
    | `SUBrm16   of 'a * 'a amode
    | `SUBrm32   of 'a * 'a amode
    | `SUBmr8    of 'a amode * 'a
    | `SUBmr16   of 'a amode * 'a
    | `SUBmr32   of 'a amode * 'a
    | `SUBr16si8 of 'a * int
    | `SUBr32si8 of 'a * int
    | `SUBm16si8 of 'a amode * int
    | `SUBm32si8 of 'a amode * int
  ] [@@deriving compare, equal, sexp]

  type 'a subsd = [
    | `SUBSDrr of 'a * 'a
    | `SUBSDrm of 'a * 'a amode
  ] [@@deriving compare, equal, sexp]

  type 'a subss = [
    | `SUBSSrr of 'a * 'a
    | `SUBSSrm of 'a * 'a amode
  ] [@@deriving compare, equal, sexp]

  type 'a test = [
    | `TESTri8  of 'a * int
    | `TESTri16 of 'a * int
    | `TESTri32 of 'a * int32
    | `TESTmi8  of 'a amode * int
    | `TESTmi16 of 'a amode * int
    | `TESTmi32 of 'a amode * int32
    | `TESTrr8  of 'a * 'a
    | `TESTrr16 of 'a * 'a
    | `TESTrr32 of 'a * 'a
    | `TESTrm8  of 'a * 'a amode
    | `TESTrm16 of 'a * 'a amode
    | `TESTrm32 of 'a * 'a amode
    | `TESTmr8  of 'a amode * 'a
    | `TESTmr16 of 'a amode * 'a
    | `TESTmr32 of 'a amode * 'a
  ] [@@deriving compare, equal, sexp]

  type 'a tzcnt = [
    | `TZCNTrr16 of 'a * 'a
    | `TZCNTrr32 of 'a * 'a
    | `TZCNTrm16 of 'a * 'a amode
    | `TZCNTrm32 of 'a * 'a amode
  ] [@@deriving compare, equal, sexp]

  type 'a ucomisd = [
    | `UCOMISDrr of 'a * 'a
    | `UCOMISDrm of 'a * 'a amode
  ] [@@deriving compare, equal, sexp]

  type 'a ucomiss = [
    | `UCOMISSrr of 'a * 'a
    | `UCOMISSrm of 'a * 'a amode
  ] [@@deriving compare, equal, sexp]

  type 'a xor = [
    | `XORri8    of 'a * int
    | `XORri16   of 'a * int
    | `XORri32   of 'a * int32
    | `XORmi8    of 'a amode * int
    | `XORmi16   of 'a amode * int
    | `XORmi32   of 'a amode * int32
    | `XORrr8    of 'a * 'a
    | `XORrr16   of 'a * 'a
    | `XORrr32   of 'a * 'a
    | `XORrm8    of 'a * 'a amode
    | `XORrm16   of 'a * 'a amode
    | `XORrm32   of 'a * 'a amode
    | `XORmr8    of 'a amode * 'a
    | `XORmr16   of 'a amode * 'a
    | `XORmr32   of 'a amode * 'a
    | `XORr16si8 of 'a * int
    | `XORr32si8 of 'a * int
    | `XORm16si8 of 'a amode * int
    | `XORm32si8 of 'a amode * int
  ] [@@deriving compare, equal, sexp]

  type 'a xorpd = [
    | `XORPDrr of 'a * 'a
    | `XORPDrm of 'a * 'a amode
  ] [@@deriving compare, equal, sexp]

  type 'a xorps = [
    | `XORPSrr of 'a * 'a
    | `XORPSrm of 'a * 'a amode
  ] [@@deriving compare, equal, sexp]
end

type 'a insn_base = [
  | 'a Insn.add
  | 'a Insn.addsd
  | 'a Insn.addss
  | 'a Insn.and_
  | 'a Insn.call
  | Insn.cdq
  | 'a Insn.cmovcc
  | 'a Insn.cmp
  | Insn.cwd
  | 'a Insn.cvtsi2sd
  | 'a Insn.cvtsi2ss
  | 'a Insn.cvtsd2si
  | 'a Insn.cvtss2si
  | 'a Insn.dec
  | 'a Insn.div
  | 'a Insn.divsd
  | 'a Insn.divss
  | 'a Insn.idiv
  | 'a Insn.imul
  | 'a Insn.inc
  | 'a Insn.jcc
  | 'a Insn.jmp
  | 'a Insn.lea
  | 'a Insn.lzcnt
  | 'a Insn.mov
  | 'a Insn.movd
  | 'a Insn.movsd
  | 'a Insn.movss
  | 'a Insn.movzx
  | 'a Insn.mul
  | 'a Insn.mulsd
  | 'a Insn.mulss
  | 'a Insn.neg
  | 'a Insn.not_
  | 'a Insn.or_
  | 'a Insn.pop
  | 'a Insn.popcnt
  | 'a Insn.push
  | 'a Insn.ret
  | 'a Insn.rol
  | 'a Insn.ror
  | 'a Insn.sar
  | 'a Insn.setcc
  | 'a Insn.shl
  | 'a Insn.shr
  | 'a Insn.sub
  | 'a Insn.subsd
  | 'a Insn.subss
  | 'a Insn.test
  | 'a Insn.tzcnt
  | 'a Insn.ucomisd
  | 'a Insn.ucomiss
  | 'a Insn.xor
  | 'a Insn.xorpd
  | 'a Insn.xorps
] [@@deriving compare, equal, sexp]
