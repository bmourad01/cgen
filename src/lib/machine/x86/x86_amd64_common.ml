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

  let sp = `rsp
  let fp = `rbp
  let scratch = `rax

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
    | `rflags
  ] [@@deriving bin_io, compare, equal, sexp]

  let typeof = function
    | #gpr | `rip | `rflags -> `i64
    | #sse -> `v128

  let is_gpr = function
    | #gpr -> true
    | #sse -> false
    | `rip | `rflags -> false

  let is_sse = function
    | #gpr -> false
    | #sse -> true
    | `rip | `rflags -> false

  let is_rip = function
    | `rip -> true
    | _ -> false

  let is_rflags = function
    | `rflags -> true
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
    | Dlbl of Label.t      (* Label *)
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
    | Dlbl l ->
      Format.fprintf ppf "%a" Label.pp l

  (* Memory addressing modes. Scale must be 1, 2, 4, or 8. *)
  type amode =
    | Ad    of disp                 (* Displacement *)
    | Ab    of rv                   (* Base *)
    | Abi   of rv * rv              (* Base + index *)
    | Abd   of rv * disp            (* Base + displacement *)
    | Abid  of rv * rv * disp       (* Base + index + displacement *)
    | Abis  of rv * rv * int        (* Base + index * scale *)
    | Ais   of rv * int             (* Index * scale *)
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
    | Abd (b, Dimm d) when Int32.(d < 0l) ->
      Format.fprintf ppf "%a - 0x%lx"
        Regvar.pp b (Int32.neg d)
    | Abd (b, d) ->
      Format.fprintf ppf "%a + %a"
        Regvar.pp b pp_disp d
    | Abid (b, i, Dimm d) when Int32.(d < 0l) ->
      Format.fprintf ppf "%a + %a*1 - 0x%lx"
        Regvar.pp b Regvar.pp i (Int32.neg d)
    | Abid (b, i, d) ->
      Format.fprintf ppf "%a + %a*1 + %a"
        Regvar.pp b Regvar.pp i pp_disp d
    | Abis (b, i, s) ->
      Format.fprintf ppf "%a + %a*%d"
        Regvar.pp b Regvar.pp i s
    | Aisd (i, s, Dimm d) when Int32.(d < 0l) ->
      Format.fprintf ppf "%a*%d - 0x%lx"
        Regvar.pp i s (Int32.neg d)
    | Ais (i, s) ->
      Format.fprintf ppf "%a*%d" Regvar.pp i s
    | Aisd (i, s, d) ->
      Format.fprintf ppf "%a*%d + %a"
        Regvar.pp i s pp_disp d
    | Abisd (b, i, s, Dimm d) when Int32.(d < 0l) ->
      Format.fprintf ppf "%a + %a*%d - 0x%lx"
        Regvar.pp b Regvar.pp i s (Int32.neg d)
    | Abisd (b, i, s, d) ->
      Format.fprintf ppf "%a + %a*%d + %a"
        Regvar.pp b Regvar.pp i s pp_disp d

  type memty = [
    | Type.basic
    | `v128
  ] [@@deriving bin_io, compare, equal, sexp]

  let pp_memty ppf = function
    | `i8 -> Format.fprintf ppf "byte ptr"
    | `i16 -> Format.fprintf ppf "word ptr"
    | `i32 -> Format.fprintf ppf "dword ptr"
    | `i64 -> Format.fprintf ppf "qword ptr"
    | `f32 -> Format.fprintf ppf "dword ptr"
    | `f64 -> Format.fprintf ppf "qword ptr"
    | `v128 -> Format.fprintf ppf "xmmword ptr"

  (* An argument to an instruction. *)
  type operand =
    | Oreg  of rv * Type.basic  (* Register *)
    | Oregv of rv               (* Vector register (special case) *)
    | Oimm  of int64 * Type.imm (* Immediate *)
    | Omem  of amode * memty    (* Memory address *)
    | Osym  of string * int     (* Symbol *)
    | Ofp32 of Float32.t        (* Single-precision floating-point number *)
    | Ofp64 of float            (* Double-precision floating-point number *)
    | Oah                       (* AH register *)
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
    | Oregv r ->
      Format.fprintf ppf "%a" Regvar.pp r
    | Oimm (i, `i64) ->
      Format.fprintf ppf "0x%Lx_%a" i Type.pp_imm `i64
    | Oimm (i, `i32) ->
      Format.fprintf ppf "0x%Lx_%a" Int64.(i land 0xFFFFFFFFL) Type.pp_imm `i32
    | Oimm (i, `i16) ->
      Format.fprintf ppf "0x%Lx_%a" Int64.(i land 0xFFFFL) Type.pp_imm `i16
    | Oimm (i, `i8) ->
      Format.fprintf ppf "0x%Lx_%a" Int64.(i land 0xFFL) Type.pp_imm `i8
    | Omem (a, t) ->
      Format.fprintf ppf "%a [%a]" pp_memty t pp_amode a
    | Osym (s, o) when o < 0 ->
      Format.fprintf ppf "$%s-%d" s (-o)
    | Osym (s, o) when o > 0 ->
      Format.fprintf ppf "$%s+%d" s o
    | Osym (s, _) ->
      Format.fprintf ppf "$%s" s
    | Ofp32 f ->
      Format.fprintf ppf "%sf" (Float32.to_string f)
    | Ofp64 f ->
      Format.fprintf ppf "%a" Float.pp f
    | Oah ->
      Format.fprintf ppf "ah"

  (* Condition codes. *)
  type cc =
    (* Unsigned comparison ("above" or "below") *)
    | Ca  (* ~CF & ~ZF *)
    | Cae (* ~CF *)
    | Cb  (* CF *)
    | Cbe (* CF | ZF *)
    (* Equality *)
    | Ce  (* ZF *)
    | Cne (* ~ZF *)
    (* Signed comparison ("greater" or "less") *)
    | Cg  (* ~ZF & SF=OF *)
    | Cge (* SF=OF *)
    | Cl  (* SF<>OF *)
    | Cle (* ZF | SF<>OF *)
    (* Parity bit *)
    | Cp  (* PF *)
    | Cnp (* ~PF *)
    (* Sign bit *)
    | Cs  (* SF *)
    | Cns (* ~SF *)
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
    | Cs  -> Format.fprintf ppf "s"
    | Cns -> Format.fprintf ppf "ns"

  (* [Jind (a, ls)]: indirect jump to [o], with an optional set of
     static labels [ls].

     [Jlbl l]: direct jump to label [l]
  *)
  type jmp =
    | Jind of operand
    | Jlbl of Label.t
  [@@deriving bin_io, compare, equal, sexp]

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
    | CVTSD2SS of operand * operand
    | CVTSI2SD of operand * operand
    | CVTSI2SS of operand * operand
    | CVTSS2SI of operand * operand
    | CVTSS2SD of operand * operand
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
    | JMP      of jmp
    | LEA      of operand * operand
    | LZCNT    of operand * operand
    | MOV      of operand * operand
    | MOVD     of operand * operand
    | MOVDQA   of operand * operand
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
    | TEST_    of operand * operand
    | TZCNT    of operand * operand
    | UCOMISD  of operand * operand
    | UCOMISS  of operand * operand
    | UD2
    | XOR      of operand * operand
    | XORPD    of operand * operand
    | XORPS    of operand * operand
    (* Same as `MOV`, but we want to force the zero-extension,
       so this shouldn't be a target of peephole opts. *)
    | MOV_     of operand * operand
    (* Pseudo-instruction we will use to represent a jump table. *)
    | JMPtbl   of Label.t * Label.t list
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
    | CVTSD2SS (a, b) -> binary "cvtsd2ss" a b
    | CVTSI2SD (a, b) -> binary "cvtsi2sd" a b
    | CVTSI2SS (a, b) -> binary "cvtsi2ss" a b
    | CVTSS2SI (a, b) -> binary "cvtss2si" a b
    | CVTSS2SD (a, b) -> binary "cvtss2sd" a b
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
    | JMP (Jind a) -> unary "jmp" a
    | JMP (Jlbl l) ->
      Format.fprintf ppf "jmp %a" Label.pp l
    | LEA (a, b) -> binary "lea" a b
    | LZCNT (a, b) -> binary "lzcnt" a b
    | MOV (a, b) -> binary "mov" a b
    | MOVD (a, b) -> binary "movd" a b
    | MOVDQA (a, b) -> binary "movdqa" a b
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
    | TEST_ (a, b) -> binary "test" a b
    | TZCNT (a, b) -> binary "tzcnt" a b
    | UCOMISD (a, b) -> binary "ucomisd" a b
    | UCOMISS (a, b) -> binary "ucomiss" a b
    | UD2 -> Format.fprintf ppf "ud2"
    | XOR (a, b) -> binary "xor" a b
    | XORPD (a, b) -> binary "xorpd" a b
    | XORPS (a, b) -> binary "xorps" a b
    | MOV_ (a, b) ->
      binary "mov" a b;
      (* Make a little note here. *)
      Format.fprintf ppf " ; zx"
    | JMPtbl (l, ls) ->
      let pp_sep ppf () = Format.fprintf ppf ", " in
      Format.fprintf ppf ".tbl %a [@[%a@]]"
        Label.pp l
        (Format.pp_print_list ~pp_sep Label.pp)
        ls

  (* Helper for registers mentioned in an addressing mode. *)
  let rv_of_amode = function
    | Ad _ -> []
    | Ab a -> [a]
    | Abi (a, b) ->  [a; b]
    | Abd (a, _) -> [a]
    | Abid (a, b, _) -> [a; b]
    | Abis (a, b, _) -> [a; b]
    | Ais (a, _) -> [a]
    | Aisd (a, _, _) -> [a]
    | Abisd (a, b, _, _) -> [a; b]

  (* All registers mentioned in operands. *)
  let rset operands =
    Regvar.Set.of_list @@
    List.bind operands ~f:(function
        | Oreg (a, _) | Oregv a -> [a]
        | Omem (a, _) -> rv_of_amode a
        | Oah -> [Reg `rax]
        | _ -> [])

  (* Only explicit register operands. *)
  let rset_reg operands =
    Regvar.Set.of_list @@
    List.bind operands ~f:(function
        | Oreg (a, _) | Oregv a -> [a]
        | Oah -> [Reg `rax]
        | _ -> [])

  (* Only registers mentioned in memory operands. *)
  let rset_mem operands =
    Regvar.Set.of_list @@
    List.bind operands ~f:(function
        | Omem (a, _) -> rv_of_amode a
        | _ -> [])

  (* Hardcoded registers. *)
  let rset' regs =
    Regvar.Set.of_list @@
    List.map regs ~f:(fun r -> Regvar.Reg r)

  (* Registers read by an instruction. *)
  let reads call = function
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
    | TEST_ (a, b)
    | UCOMISD (a, b)
    | UCOMISS (a, b)
    | XOR (a, b)
    | XORPD (a, b)
    | XORPS (a, b)
      -> rset [a; b]
    | CALL a ->
      Set.union (rset' [`rsp]) @@
      Set.union (rset_mem [a]) call
    | PUSH a
      -> Set.union (rset' [`rsp]) (rset_mem [a])
    | CMOVcc (_, a, b)
      (* We introduce a dependency on `a` so that any previous
         writes to it will be preserved.

         This is morally equivalent to:

         `x := cc ? b : a`
      *)
      ->
      Set.union (rset' [`rflags])
        (Set.union (rset_reg [a]) (rset [b]))
    | CVTSD2SI (_, a)
    | CVTSD2SS (_, a)
    | CVTSI2SD (_, a)
    | CVTSI2SS (_, a)
    | CVTSS2SI (_, a)
    | CVTSS2SD (_, a)
    | DEC a
    | IMUL3 (_, a, _)
    | INC a
    | JMP (Jind a)
    | LEA (_, a)
    | LZCNT (_, a)
    | MOVSX (_, a)
    | MOVSXD (_, a)
    | MOVZX (_, a)
    | NEG a
    | NOT a
    | POPCNT (_, a)
    | TZCNT (_, a)
      -> rset [a]
    | MOV (a, b)
    | MOV_ (a, b)
    | MOVD (a, b)
    | MOVDQA (a, b)
    | MOVQ (a, b)
    | MOVSD (a, b)
    | MOVSS (a, b)
      -> Set.union (rset_mem [a]) (rset [b])
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
      -> rset' [`rflags]
    | SETcc (_, a)
      (* SETcc will "read" the destination in the sense that
         only the lower 8 bits are changed. *)
      -> Set.union (rset' [`rflags]) (rset [a])
    | JMP (Jlbl _)
    | UD2
    | JMPtbl _
      -> Regvar.Set.empty
    | POP a
      -> Set.union (rset' [`rsp]) (rset_mem [a])
    | RET
      -> rset' [`rsp]

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
      -> Set.union (rset' [`rflags]) (rset_reg [a])
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
      -> rset_reg [a]
    | CALL _
      -> Set.union (rset' [`rsp; `rflags]) call
    | PUSH _
    | RET
      -> rset' [`rsp]
    | CMP _
    | TEST_ _
    | UCOMISD _
    | UCOMISS _
      -> rset' [`rflags]
    | Jcc _
    | JMP _
    | UD2
    | JMPtbl _
      -> Regvar.Set.empty
    (* Special case for 8-bit div/mul. *)
    | DIV Oreg (_, `i8)
    | IDIV Oreg (_, `i8)
    | IMUL1 Oreg (_, `i8)
    | MUL Oreg (_, `i8)
      -> rset' [`rax; `rflags]
    | CDQ
    | CQO
    | CWD
      -> rset' [`rdx]
    | DIV _
    | IDIV _
    | IMUL1 _
    | MUL _
      -> rset' [`rax; `rdx; `rflags]
    | POP a
      -> Set.union (rset' [`rsp]) (rset_reg [a])

  let dests = function
    | Jcc (_, l) | JMP (Jlbl l) -> Label.Set.singleton l
    | JMPtbl (_, ls) -> Label.Set.of_list ls
    | _ -> Label.Set.empty

  let is_mem = function
    | Omem _ -> true
    | _ -> false

  (* "illegal" here means that it is illegal to have a memory
     operand in the destination. *)
  let writes_to_memory = function
    | ADD (a, _)
    | ADDSD (a, _)
    | ADDSS (a, _)
    | AND (a, _)
    | DEC a
    | DIVSD (a, _)
    | DIVSS (a, _)
    | INC a
    | MOV (a, _)
    | MOV_ (a, _)
    | MOVD (a, _)
    | MOVDQA (a, _)
    | MOVQ (a, _)
    | MOVSD (a, _)
    | MOVSS (a, _)
    | MULSD (a, _)
    | MULSS (a, _)
    | NEG a
    | NOT a
    | OR (a, _)
    | POP a
    | ROL (a, _)
    | ROR (a, _)
    | SAR (a, _)
    | SETcc (_, a)
    | SHL (a, _)
    | SHR (a, _)
    | SUB (a, _)
    | SUBSD (a, _)
    | SUBSS (a, _)
    | XOR (a, _)
      -> is_mem a
    | CALL _ (* writes to stack *)
    | PUSH _ (* writes to stack *)
      -> true
    | CDQ
    | CMOVcc _ (* illegal *)
    | CMP _
    | CQO
    | CWD
    | CVTSD2SI _ (* illegal *)
    | CVTSD2SS _ (* illegal *)
    | CVTSI2SD _ (* illegal *)
    | CVTSI2SS _ (* illegal *)
    | CVTSS2SI _ (* illegal *)
    | CVTSS2SD _ (* illegal *)
    | DIV _
    | IDIV _
    | IMUL1 _
    | IMUL2 _
    | IMUL3 _
    | Jcc _
    | JMP _
    | LEA _ (* illegal *)
    | LZCNT _ (* illegal *)
    | MOVSX _ (* illegal *)
    | MOVZX _ (* illegal *)
    | MOVSXD _ (* illegal *)
    | MUL _
    | POPCNT _ (* illegal *)
    | RET (* XXX: is this OK? *)
    | TEST_ _
    | TZCNT _
    | UCOMISD _
    | UCOMISS _
    | UD2
    | XORPD _ (* illegal *)
    | XORPS _ (* illegal *)
    | JMPtbl _ (* fake *)
      -> false

  let always_live = function
    | Jcc _
    | JMP _
    | CALL _
    | RET
    | UD2
    | JMPtbl _
      -> true
    (* Special case for zeroing a register. *)
    | XOR (Oreg (a, _), Oreg (b, _))
    | XORPD (Oreg (a, _), Oreg (b, _))
      when Regvar.equal a b -> true
    | i -> writes_to_memory i
end
