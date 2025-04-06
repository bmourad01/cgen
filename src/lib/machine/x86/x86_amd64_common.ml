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
  ] [@@deriving bin_io, compare, equal, hash, sexp]

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
  ] [@@deriving bin_io, compare, equal, hash, sexp]

  let pp_sse ppf sse =
    Format.fprintf ppf "%a" Sexp.pp (sexp_of_sse sse)

  type t = [
    | gpr
    | sse
    | `rip
    | `rflags
  ] [@@deriving bin_io, compare, equal, hash, sexp]

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

  let classof : t -> Machine_regvar.cls = function
    | #gpr | `rip | `rflags -> GPR
    | #sse -> FP

  let pp ppf r =
    Format.fprintf ppf "%a" Sexp.pp (sexp_of_t r)

  let of_string s =
    Option.try_with @@ fun () -> t_of_sexp @@ Atom s

  let of_string_exn s = match of_string s with
    | None -> invalid_argf "%s is not a valid AMD64 register" s ()
    | Some r -> r
end

module Regvar = Machine_regvar.Make(Reg)(struct
    let module_name = "Cgen.Machine.X86_amd64_common.Regvar"
  end)

type rv = Regvar.t [@@deriving bin_io, compare, equal, hash, sexp]

module Insn = struct
  (* SIB scale. Only 1, 2, 4, and 8 are valid. *)
  type scale =
    | S1
    | S2
    | S4
    | S8
  [@@deriving bin_io, compare, equal, sexp]

  let int_of_scale = function
    | S1 -> 1
    | S2 -> 2
    | S4 -> 4
    | S8 -> 8

  let pp_scale ppf s = Format.fprintf ppf "%d" @@ int_of_scale s

  (* Memory addressing modes. *)
  type amode =
    | Ab    of rv                      (* Base *)
    | Abd   of rv * int32              (* Base + displacement *)
    | Abis  of rv * rv * scale         (* Base + index * scale *)
    | Aisd  of rv * scale * int32      (* Index * scale + displacement *)
    | Abisd of rv * rv * scale * int32 (* Base + index * scale + displacement *)
    | Albl  of Label.t * int           (* RIP + label + offset *)
    | Asym  of string * int            (* RIP + symbol + offset *)
  [@@deriving bin_io, compare, equal, sexp]

  let pp_amode ppf = function
    | Ab b ->
      Format.fprintf ppf "%a" Regvar.pp b
    | Abd (b, d) when Int32.(d < 0l) ->
      Format.fprintf ppf "%a - 0x%lx"
        Regvar.pp b (Int32.neg d)
    | Abd (b, d) ->
      Format.fprintf ppf "%a + 0x%lx" Regvar.pp b d
    | Abis (b, i, s) ->
      Format.fprintf ppf "%a + %a*%a"
        Regvar.pp b Regvar.pp i pp_scale s
    | Aisd (i, s, d) when Int32.(d < 0l) ->
      Format.fprintf ppf "%a*%a - 0x%lx"
        Regvar.pp i pp_scale s (Int32.neg d)
    | Aisd (i, s, d) ->
      Format.fprintf ppf "%a*%a + 0x%lx"
        Regvar.pp i pp_scale s d
    | Abisd (b, i, s, d) when Int32.(d < 0l) ->
      Format.fprintf ppf "%a + %a*%a - 0x%lx"
        Regvar.pp b Regvar.pp i pp_scale s (Int32.neg d)
    | Abisd (b, i, s, d) ->
      Format.fprintf ppf "%a + %a*%a + 0x%lx"
        Regvar.pp b Regvar.pp i pp_scale s d
    | Asym (s, o) when o < 0 ->
      Format.fprintf ppf "rip + $%s-%d" s (-o)
    | Asym (s, o) when o > 0 ->
      Format.fprintf ppf "rip + $%s+%d" s o
    | Asym (s, _) ->
      Format.fprintf ppf "rip + $%s" s
    | Albl (l, o) when o < 0 ->
      Format.fprintf ppf "rip + %a-%d" Label.pp l (-o)
    | Albl (l, o) when o > 0 ->
      Format.fprintf ppf "rip + %a+%d" Label.pp l o
    | Albl (l, _) ->
      Format.fprintf ppf "rip + %a" Label.pp l


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
    | Oah                       (* AH register *)
  [@@deriving bin_io, compare, equal, sexp]

  let pp_operand ppf = function
    (* Print the correct register syntax based on the type. *)
    | Oreg (rv, t) ->
      begin match Regvar.which rv, t with
        | First (#Reg.sse as r), #Type.fp ->
          Format.fprintf ppf "%a" Reg.pp_sse r
        | First (#Reg.gpr as r), `i8 ->
          Format.fprintf ppf "%a" Reg.pp_gpr8 r
        | First (#Reg.gpr as r), `i16 ->
          Format.fprintf ppf "%a" Reg.pp_gpr16 r
        | First (#Reg.gpr as r), `i32 ->
          Format.fprintf ppf "%a" Reg.pp_gpr32 r
        | First (#Reg.gpr as r), `i64 ->
          Format.fprintf ppf "%a" Reg.pp_gpr r
        | _ ->
          (* This should always be a variable in practice, but we
             won't enforce it here. *)
          Format.fprintf ppf "%a:%a" Regvar.pp rv Type.pp_basic t
      end
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

  (* For swapping the order of arguments to a comparison. *)
  let flip_cc = function
    | Ca -> Cbe
    | Cae -> Cb
    | Cb -> Cae
    | Cbe -> Ca
    | Ce -> Ce
    | Cne -> Cne
    | Cg -> Cle
    | Cge -> Cl
    | Cl -> Cge
    | Cle -> Cg
    (* XXX: is this correct? *)
    | Cp -> Cp
    | Cnp -> Cnp
    | Cs -> Cs
    | Cns -> Cns

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

  type unop =
    | CALL of Regvar.t list (* arguments *)
    | DEC
    | DIV
    | IDIV
    | IMUL1
    | INC
    | MUL
    | NEG
    | NOT
    | POP
    | PUSH
    | SETcc of cc
  [@@deriving bin_io, compare, equal, sexp]

  let pp_unop ppf = function
    | CALL _ -> Format.fprintf ppf "call"
    | DEC -> Format.fprintf ppf "dec"
    | DIV -> Format.fprintf ppf "div"
    | IDIV -> Format.fprintf ppf "idiv"
    | IMUL1 -> Format.fprintf ppf "imul"
    | INC -> Format.fprintf ppf "inc"
    | MUL -> Format.fprintf ppf "mul"
    | NEG -> Format.fprintf ppf "neg"
    | NOT -> Format.fprintf ppf "not"
    | POP -> Format.fprintf ppf "pop"
    | PUSH -> Format.fprintf ppf "push"
    | SETcc cc -> Format.fprintf ppf "set%a" pp_cc cc

  type binop =
    | ADD
    | ADDSD
    | ADDSS
    | AND
    | CMOVcc of cc
    | CMP
    | CVTSD2SI
    | CVTSD2SS
    | CVTSI2SD
    | CVTSI2SS
    | CVTSS2SD
    | CVTSS2SI
    | DIVSD
    | DIVSS
    | IMUL2
    | LEA
    | LZCNT
    | MOV
    | MOVD
    | MOVDQA
    | MOVQ
    | MOVSD
    | MOVSS
    | MOVSX
    | MOVSXD
    | MOVZX
    | MULSD
    | MULSS
    | OR
    | POPCNT
    | ROL
    | ROR
    | SAR
    | SHL
    | SHR
    | SUB
    | SUBSD
    | SUBSS
    | TEST_
    | TZCNT
    | UCOMISD
    | UCOMISS
    | XOR
    | XORPD
    | XORPS
    (* Same as `MOV`, but we want to force the zero-extension,
       so this shouldn't be a target of peephole opts. *)
    | MOV_
  [@@deriving bin_io, compare, equal, sexp]

  let pp_binop ppf = function
    | ADD -> Format.fprintf ppf "add"
    | ADDSD -> Format.fprintf ppf "addsd"
    | ADDSS -> Format.fprintf ppf "addss"
    | AND -> Format.fprintf ppf "and"
    | CMOVcc cc -> Format.fprintf ppf "cmov%a" pp_cc cc
    | CMP -> Format.fprintf ppf "cmp"
    | CVTSD2SI -> Format.fprintf ppf "cvtsd2si"
    | CVTSD2SS -> Format.fprintf ppf "cvtsd2ss"
    | CVTSI2SD -> Format.fprintf ppf "cvtsi2sd"
    | CVTSI2SS -> Format.fprintf ppf "cvtsi2ss"
    | CVTSS2SD -> Format.fprintf ppf "cvtss2sd"
    | CVTSS2SI -> Format.fprintf ppf "cvtss2si"
    | DIVSD -> Format.fprintf ppf "divsd"
    | DIVSS -> Format.fprintf ppf "divss"
    | IMUL2 -> Format.fprintf ppf "imul"
    | LEA -> Format.fprintf ppf "lea"
    | LZCNT -> Format.fprintf ppf "lzcnt"
    | MOV -> Format.fprintf ppf "mov"
    | MOVD -> Format.fprintf ppf "movd"
    | MOVDQA -> Format.fprintf ppf "movdqa"
    | MOVQ -> Format.fprintf ppf "movq"
    | MOVSD -> Format.fprintf ppf "movsd"
    | MOVSS -> Format.fprintf ppf "movss"
    | MOVSX -> Format.fprintf ppf "movsx"
    | MOVSXD -> Format.fprintf ppf "movsxd"
    | MOVZX -> Format.fprintf ppf "movzx"
    | MULSD -> Format.fprintf ppf "mulsd"
    | MULSS -> Format.fprintf ppf "mulss"
    | OR -> Format.fprintf ppf "or"
    | POPCNT -> Format.fprintf ppf "popcnt"
    | ROL -> Format.fprintf ppf "rol"
    | ROR -> Format.fprintf ppf "ror"
    | SAR -> Format.fprintf ppf "sar"
    | SHL -> Format.fprintf ppf "shl"
    | SHR -> Format.fprintf ppf "shr"
    | SUB -> Format.fprintf ppf "sub"
    | SUBSD -> Format.fprintf ppf "subsd"
    | SUBSS -> Format.fprintf ppf "subss"
    | TEST_ -> Format.fprintf ppf "test"
    | TZCNT -> Format.fprintf ppf "tzcnt"
    | UCOMISD -> Format.fprintf ppf "ucomisd"
    | UCOMISS -> Format.fprintf ppf "ucomiss"
    | XOR -> Format.fprintf ppf "xor"
    | XORPD -> Format.fprintf ppf "xorpd"
    | XORPS -> Format.fprintf ppf "xorpss"
    | MOV_ -> Format.fprintf ppf "mov"

  type t =
    | One of unop * operand
    | Two of binop * operand * operand
    | CDQ
    | CQO
    | CWD
    | IMUL3 of operand * operand * int32
    | Jcc of cc * Label.t
    | JMP of jmp
    | RET
    | UD2
    (* Pseudo-instruction we will use to represent a jump table. *)
    | JMPtbl of Label.t * Label.t list
    (* Pseudo instructions for floating-point constants. *)
    | FP32 of Label.t * Float32.t
    | FP64 of Label.t * float
  [@@deriving bin_io, compare, equal, sexp]

  let pp ppf = function
    | One (op, a) ->
      Format.fprintf ppf "%a %a" pp_unop op pp_operand a;
      begin match op with
        | CALL [] -> ()
        | CALL args ->
          let pp_sep ppf () = Format.fprintf ppf " " in
          Format.fprintf ppf " ; %a"
            (Format.pp_print_list ~pp_sep Regvar.pp)
            args
        | _ -> ()
      end
    | Two (op, a, b) ->
      Format.fprintf ppf "%a %a, %a"
        pp_binop op pp_operand a pp_operand b;
      if equal_binop op MOV_ then
        Format.fprintf ppf " ; zx";
    | CDQ ->
      Format.fprintf ppf "cdq"
    | CQO ->
      Format.fprintf ppf "cqo"
    | CWD ->
      Format.fprintf ppf "cwd"
    | IMUL3 (a, b, c) ->
      Format.fprintf ppf "imul %a, %a, 0x%lx"
        pp_operand a pp_operand b c
    | Jcc (cc, l) ->
      Format.fprintf ppf "j%a %a"
        pp_cc cc Label.pp l
    | JMP (Jind a) ->
      Format.fprintf ppf "jmp %a" pp_operand a
    | JMP (Jlbl l) ->
      Format.fprintf ppf "jmp %a" Label.pp l
    | RET ->
      Format.fprintf ppf "ret"
    | UD2 ->
      Format.fprintf ppf "ud2"
    | JMPtbl (l, ls) ->
      let pp_sep ppf () = Format.fprintf ppf ", " in
      Format.fprintf ppf ".tbl %a [@[%a@]]"
        Label.pp l
        (Format.pp_print_list ~pp_sep Label.pp)
        ls
    | FP32 (l, f) ->
      Format.fprintf ppf ".fp32 %a, %s" Label.pp l (Float32.to_string f)
    | FP64 (l, f) ->
      Format.fprintf ppf ".fp64 %a, %a" Label.pp l Float.pp f

  (* Helper for registers mentioned in an addressing mode. *)
  let rv_of_amode = function
    | Ab a -> [a]
    | Abd (a, _) -> [a]
    | Abis (a, b, _) -> [a; b]
    | Aisd (a, _, _) -> [a]
    | Abisd (a, b, _, _) -> [a; b]
    | Asym _ | Albl _ -> [Regvar.reg `rip]

  (* All registers mentioned in operands. *)
  let rset operands =
    Regvar.Set.of_list @@
    List.bind operands ~f:(function
        | Oreg (a, _) | Oregv a -> [a]
        | Omem (a, _) -> rv_of_amode a
        | Oah -> [Regvar.reg `rax]
        | _ -> [])

  (* Only explicit register operands. *)
  let rset_reg operands =
    Regvar.Set.of_list @@
    List.bind operands ~f:(function
        | Oreg (a, _) | Oregv a -> [a]
        | Oah -> [Regvar.reg `rax]
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
    List.map regs ~f:Regvar.reg

  (* Registers read by an instruction. *)
  let reads = function
    | Two (op, a, b) ->
      begin match op with
        | ADD
        | ADDSD
        | ADDSS
        | AND
        | CMP
        | DIVSD
        | DIVSS
        | IMUL2
        | MULSD
        | MULSS
        | OR
        | ROL
        | ROR
        | SAR
        | SHL
        | SHR
        | SUB
        | SUBSD
        | SUBSS
        | TEST_
        | UCOMISD
        | UCOMISS
          -> rset [a; b]
        | CMOVcc _
          (* We introduce a dependency on `a` so that any previous
             writes to it will be preserved.

             This is morally equivalent to:

             `x := cc ? b : a`
          *)
          ->
          Set.union (rset' [`rflags])
            (Set.union (rset_reg [a]) (rset [b]))
        | CVTSD2SI
        | CVTSD2SS
        | CVTSI2SD
        | CVTSI2SS
        | CVTSS2SD
        | CVTSS2SI
        | LEA
        | LZCNT
        | MOVSX
        | MOVSXD
        | MOVZX
        | POPCNT
        | TZCNT
          -> rset [b]
        | MOV
        | MOV_
        | MOVD
        | MOVDQA
        | MOVQ
        | MOVSD
        | MOVSS
          -> Set.union (rset_mem [a]) (rset [b])
        | XOR
        | XORPD
        | XORPS ->
          begin match a, b with
            | Oreg (a, _), Oreg (b, _) when Regvar.(a = b)
              (* Special case for XORing with self: this isn't really a use
                 of the register, since we're just assigning 0. *)
              -> Regvar.Set.empty
            | _ -> rset [a; b]
          end
      end
    | One (op, a) ->
      begin match op with
        | CALL args ->
          Set.union (rset' [`rsp]) @@
          Set.union (rset_mem [a]) @@
          Regvar.Set.of_list args
        | DEC
        | INC
        | NEG
        | NOT
          -> rset [a]
        | DIV
        | IDIV ->
          begin match a with
            | Oreg (_, `i8)
              -> Set.union (rset' [`rax]) (rset [a])
            | _ 
              -> Set.union (rset' [`rax; `rdx]) (rset [a])
          end
        | IMUL1
        | MUL
          -> Set.union (rset' [`rax]) (rset [a])
        | SETcc _
          (* SETcc will "read" the destination in the sense that
             only the lower 8 bits are changed. *)
          -> Set.union (rset' [`rflags]) (rset [a])
        | POP
        | PUSH
          -> Set.union (rset' [`rsp]) (rset_mem [a])
      end
    | JMP (Jind a) -> rset [a]
    | CDQ
    | CQO
    | CWD
      -> rset' [`rax]
    | IMUL3 (_, b, _)
      -> rset [b]
    | Jcc _
      -> rset' [`rflags]
    | JMP (Jlbl _)
      -> Regvar.Set.empty
    | RET
      -> rset' [`rsp]
    | UD2
    | JMPtbl _
    | FP32 _
    | FP64 _
      -> Regvar.Set.empty

  (* Registers written to by an instruction. *)
  let writes call = function
    | Two (op, a, _) ->
      begin match op with
        | ADD
        | AND
        | IMUL2
        | LZCNT
        | OR
        | POPCNT
        | ROL
        | ROR
        | SAR
        | SHL
        | SHR
        | SUB
        | XOR
          -> Set.union (rset' [`rflags]) (rset_reg [a])
        | ADDSD
        | ADDSS
        | CMOVcc _
        | CVTSD2SI
        | CVTSD2SS
        | CVTSI2SD
        | CVTSI2SS
        | CVTSS2SD
        | CVTSS2SI
        | DIVSD
        | DIVSS
        | LEA
        | MOV
        | MOV_
        | MOVD
        | MOVDQA
        | MOVQ
        | MOVSD
        | MOVSS
        | MOVSX
        | MOVSXD
        | MOVZX
        | MULSD
        | MULSS
        | SUBSD
        | SUBSS
        | TZCNT
        | XORPD
        | XORPS
          -> rset_reg [a]
        | CMP
        | TEST_
        | UCOMISD
        | UCOMISS
          -> rset' [`rflags]
      end
    | One (op, a) ->
      begin match op with
        | DEC
        | INC
        | NEG
        | NOT
          -> Set.union (rset' [`rflags]) (rset_reg [a])
        | SETcc _
          -> rset_reg [a]
        | CALL _
          -> Set.union (rset' [`rsp; `rflags]) call
        | PUSH
          -> rset' [`rsp]
        | DIV
        | IDIV
        | IMUL1
        | MUL ->
          begin match a with
            | Oreg (_, `i8)
              -> rset' [`rax; `rflags]
            | _
              -> rset' [`rax; `rdx; `rflags]
          end
        | POP
          -> Set.union (rset' [`rsp]) (rset_reg [a])
      end
    | IMUL3 (a, _, _)
      -> Set.union (rset' [`rflags]) (rset_reg [a])
    | RET
      -> rset' [`rsp]
    | Jcc _
    | JMP _
    | UD2
    | JMPtbl _
    | FP32 _
    | FP64 _
      -> Regvar.Set.empty
    | CDQ
    | CQO
    | CWD
      -> rset' [`rdx]

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
    | Two (op, a, _) ->
      begin match op with
        | ADD
        | ADDSD
        | ADDSS
        | AND
        | DIVSD
        | DIVSS
        | MOV
        | MOV_
        | MOVD
        | MOVDQA
        | MOVQ
        | MOVSD
        | MOVSS
        | MULSD
        | MULSS
        | OR
        | ROL
        | ROR
        | SAR
        | SHL
        | SHR
        | SUB
        | SUBSD
        | SUBSS
        | XOR
          -> is_mem a
        | CMOVcc _ (* illegal *)
        | CMP
        | CVTSD2SI (* illegal *)
        | CVTSD2SS (* illegal *)
        | CVTSI2SD (* illegal *)
        | CVTSI2SS (* illegal *)
        | CVTSS2SI (* illegal *)
        | CVTSS2SD (* illegal *)
        | IMUL2
        | LEA  (* illegal *)
        | LZCNT (* illegal *)
        | MOVSX (* illegal *)
        | MOVZX (* illegal *)
        | MOVSXD (* illegal *)
        | POPCNT (* illegal *)
        | TEST_
        | TZCNT
        | UCOMISD
        | UCOMISS
        | XORPD (* illegal *)
        | XORPS (* illegal *)
          -> false
      end
    | One (op, a) ->
      begin match op with
        | DEC
        | INC
        | NEG
        | NOT
        | POP
        | SETcc _
          -> is_mem a
        | CALL _ (* writes to stack *)
        | PUSH (* writes to stack *)
          -> true
        | DIV
        | IDIV
        | IMUL1
        | MUL
          -> false
      end
    | CDQ
    | CQO
    | CWD
    | Jcc _
    | JMP _
    | RET (* XXX: is this OK? *)
    | UD2
    | JMPtbl _ (* fake *)
    | FP32 _ (* fake *)
    | FP64 _ (* fake *)
    | IMUL3 _
      -> false

  let always_live = function
    | Jcc _
    | JMP _
    | One (CALL _, _)
    | RET
    | UD2
    | JMPtbl _
    | FP32 _
    | FP64 _
      -> true
    (* Special case for zeroing a register. *)
    | Two (XOR, Oreg (a, _), Oreg (b, _))
    | Two (XORPD, Oreg (a, _), Oreg (b, _))
    | Two (XORPS, Oreg (a, _), Oreg (b, _))
      when Regvar.equal a b -> true
    | i -> writes_to_memory i

  let is_return = function
    | RET -> true
    | _ -> false

  module I = struct
    let add a b = Two (ADD, a, b)
    let addsd a b = Two (ADDSD, a, b)
    let addss a b = Two (ADDSS, a, b)
    let and_ a b = Two (AND, a, b)
    let cmov cc a b = Two (CMOVcc cc, a, b)
    let cmp a b = Two (CMP, a, b)
    let cvtsd2si a b = Two (CVTSD2SI, a, b)
    let cvtsd2ss a b = Two (CVTSD2SS, a, b)
    let cvtsi2sd a b = Two (CVTSI2SD, a, b)
    let cvtsi2ss a b = Two (CVTSI2SS, a, b)
    let cvtss2sd a b = Two (CVTSS2SD, a, b)
    let cvtss2si a b = Two (CVTSS2SI, a, b)
    let divsd a b = Two (DIVSD, a, b)
    let divss a b = Two (DIVSS, a, b)
    let imul2 a b = Two (IMUL2, a, b)
    let lea a b = Two (LEA, a, b)
    let lzcnt a b = Two (LZCNT, a, b)
    let mov a b = Two (MOV, a, b)
    let mov_ a b = Two (MOV_, a, b)
    let movd a b = Two (MOVD, a, b)
    let movdqa a b = Two (MOVDQA, a, b)
    let movq a b = Two (MOVQ, a, b)
    let movsd a b = Two (MOVSD, a, b)
    let movss a b = Two (MOVSS, a, b)
    let movsx a b = Two (MOVSX, a, b)
    let movsxd a b = Two (MOVSXD, a, b)
    let movzx a b = Two (MOVZX, a, b)
    let mulsd a b = Two (MULSD, a, b)
    let mulss a b = Two (MULSS, a, b)
    let or_ a b = Two (OR, a, b)
    let popcnt a b = Two (POPCNT, a, b)
    let rol a b = Two (ROL, a, b)
    let ror a b = Two (ROR, a, b)
    let sar a b = Two (SAR, a, b)
    let shl a b = Two (SHL, a, b)
    let shr a b = Two (SHR, a, b)
    let sub a b = Two (SUB, a, b)
    let subsd a b = Two (SUBSD, a, b)
    let subss a b = Two (SUBSS, a, b)
    let test a b = Two (TEST_, a, b)
    let tzcnt a b = Two (TZCNT, a, b)
    let ucomisd a b = Two (UCOMISD, a, b)
    let ucomiss a b = Two (UCOMISS, a, b)
    let xor a b = Two (XOR, a, b)
    let xorpd a b = Two (XORPD, a, b)
    let xorps a b = Two (XORPS, a, b)

    let call args a = One (CALL args, a)
    let dec a = One (DEC, a)
    let div a = One (DIV, a)
    let idiv a = One (IDIV, a)
    let imul1 a = One (IMUL1, a)
    let inc a = One (INC, a)
    let mul a = One (MUL, a)
    let neg a = One (NEG, a)
    let not_ a = One (NOT, a)
    let pop a = One (POP, a)
    let push a = One (PUSH, a)
    let setcc cc a = One (SETcc cc, a)

    let cdq = CDQ
    let cqo = CQO
    let cwd = CWD
    let imul3 a b c = IMUL3 (a, b, c)
    let jcc cc a = Jcc (cc, a)
    let jmp a = JMP a
    let ret = RET
    let ud2 = UD2
    let jmptbl l ls = JMPtbl (l, ls)
    let fp32 l f = FP32 (l, f)
    let fp64 l f = FP64 (l, f)
  end
end
