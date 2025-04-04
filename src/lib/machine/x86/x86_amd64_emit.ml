open Core
open Regular.Std
open X86_amd64_common

module Data = Virtual.Data

let global ppf name =
  Format.fprintf ppf ".global %s\n" name

let emit_prelude ppf name =
  Format.fprintf ppf "/* module %s */\n" name;
  Format.fprintf ppf ".intel_syntax noprefix\n"

let emit_data_elt ppf : Data.elt -> unit = function
  | `bool b ->
    Format.fprintf ppf "  .byte %d\n" @@ Bool.to_int b
  | `int (i, `i8) ->
    Format.fprintf ppf "  .byte %a\n" Bv.pp i
  | `int (i, `i16) ->
    Format.fprintf ppf "  .word %a\n" Bv.pp i
  | `int (i, `i32) ->
    Format.fprintf ppf "  .long %a\n" Bv.pp i
  | `int (i, `i64) ->
    Format.fprintf ppf "  .quad %a\n" Bv.pp i
  | `float f ->
    Format.fprintf ppf "  .single %s\n" @@ Float32.to_string f
  | `double d ->
    Format.fprintf ppf "  .double %a\n" Float.pp d
  | `sym (s, o) ->
    Format.fprintf ppf "  .quad %s" s;
    if o < 0 then Format.fprintf ppf "-%d" (-o)
    else if o > 0 then Format.fprintf ppf "+%d" o;
    Format.fprintf ppf "\n";
  | `string s ->
    Format.fprintf ppf "  .ascii %S\n" s
  | `zero n ->
    Format.fprintf ppf "  .zero %d\n" n

let emit_data ppf d =
  let name = Data.name d in
  let lnk = Data.linkage d in
  let section =
    (* If the user specified a section, then override the "const" qualifier. *)
    let default = if Data.const d then ".rodata" else ".data" in
    Linkage.section lnk |> Option.value ~default in
  Format.fprintf ppf ".section %s\n" section;
  Data.align d |> Option.iter ~f:(Format.fprintf ppf ".align %d\n");
  if Linkage.export lnk then global ppf name;
  Format.fprintf ppf "%s:\n" name;
  Data.elts d |> Seq.iter ~f:(emit_data_elt ppf)

let emit_func ppf (name, lnk) =
  let section = Linkage.section lnk |> Option.value ~default:".text" in
  Format.fprintf ppf ".section %s\n" section;
  if Linkage.export lnk then global ppf name;
  Format.fprintf ppf ".p2align 4\n";
  Format.fprintf ppf "%s:\n" name

let emit_blk ppf (l : Label.t) =
  Format.fprintf ppf ".L%a:\n" Int63.pp (l :> Int63.t)

let emit_disp ppf : Insn.disp -> unit = function
  | Dsym (s, o) when o < 0 ->
    Format.fprintf ppf "%s-%d" s (-o)
  | Dsym (s, o) when o > 0 ->
    Format.fprintf ppf "%s+%d" s o
  | Dsym (s, _) ->
    Format.fprintf ppf "%s" s
  | Dimm i ->
    Format.fprintf ppf "0x%lx" i
  | Dlbl (l, o) when o < 0 ->
    Format.fprintf ppf ".L%a-%d" Int63.pp (l :> Int63.t) (-o)
  | Dlbl (l, o) when o > 0 ->
    Format.fprintf ppf ".L%a+%d" Int63.pp (l :> Int63.t) o
  | Dlbl (l, _) ->
    Format.fprintf ppf ".L%a" Label.pp l

let emit_regvar t ppf rv = match Regvar.which rv with
  | First r ->
    begin match r, t with
      | (#Reg.sse as r), (#Type.fp | `v128) ->
        Format.fprintf ppf "%a" Reg.pp_sse r
      | (#Reg.gpr as r), `i8 ->
        Format.fprintf ppf "%a" Reg.pp_gpr8 r
      | (#Reg.gpr as r), `i16 ->
        Format.fprintf ppf "%a" Reg.pp_gpr16 r
      | (#Reg.gpr as r), `i32 ->
        Format.fprintf ppf "%a" Reg.pp_gpr32 r
      | (#Reg.gpr as r), `i64 ->
        Format.fprintf ppf "%a" Reg.pp_gpr r
      | `rip, `i64 ->
        Format.fprintf ppf "rip"
      | _ ->
        invalid_argf "invalid register/type combo: %s/%s"
          (Format.asprintf "%a" Reg.pp r)
          (match t with
           | `v128 -> "v128"
           | #Type.basic as t ->
             Format.asprintf "%a" Type.pp_basic t)
          ()
    end
  | Second (x, _) ->
    invalid_argf "tried to emit a variable %s"
      (Format.asprintf "%a" Var.pp x) ()

let emit_amode ppf (a : Insn.amode) =
  let rv = emit_regvar `i64 in
  match a with
  | Ad d ->
    Format.fprintf ppf "%a" emit_disp d
  | Ab b ->
    Format.fprintf ppf "%a" rv b
  | Abd (b, Dimm d) when Int32.(d < 0l) ->
    Format.fprintf ppf "%a - 0x%lx" rv b (Int32.neg d)
  | Abd (b, d) ->
    Format.fprintf ppf "%a + %a" rv b emit_disp d
  | Abis (b, i, s) ->
    Format.fprintf ppf "%a + %a*%a" rv b rv i Insn.pp_scale s
  | Aisd (i, s, Dimm d) when Int32.(d < 0l) ->
    Format.fprintf ppf "%a*%a - 0x%lx"
      rv i Insn.pp_scale s (Int32.neg d)
  | Aisd (i, s, d) ->
    Format.fprintf ppf "%a*%a + %a"
      rv i Insn.pp_scale s emit_disp d
  | Abisd (b, i, s, Dimm d) when Int32.(d < 0l) ->
    Format.fprintf ppf "%a + %a*%a - 0x%lx"
      rv b rv i Insn.pp_scale s (Int32.neg d)
  | Abisd (b, i, s, d) ->
    Format.fprintf ppf "%a + %a*%a + %a"
      rv b rv i Insn.pp_scale s Insn.pp_disp d

let emit_operand ppf : Insn.operand -> unit = function
  | Oreg (rv, t) ->
    Format.fprintf ppf "%a" (emit_regvar (t :> Insn.memty)) rv
  | Oregv rv ->
    Format.fprintf ppf "%a" (emit_regvar `v128) rv
  | Oimm (i, `i8) ->
    Format.fprintf ppf "0x%Lx" Int64.(i land 0xFFL)
  | Oimm (i, `i16) ->
    Format.fprintf ppf "0x%Lx" Int64.(i land 0xFFFFL)
  | Oimm (i, `i32) ->
    Format.fprintf ppf "0x%Lx" Int64.(i land 0xFFFF_FFFFL)
  | Oimm (i, `i64) ->
    Format.fprintf ppf "0x%Lx" i
  | Omem (a, t) ->
    Format.fprintf ppf "%a [%a]" Insn.pp_memty t emit_amode a
  | Osym (s, o) when o < 0 ->
    Format.fprintf ppf "%s-%d" s (-o)
  | Osym (s, o) when o > 0 ->
    Format.fprintf ppf "%s+%d" s o
  | Osym (s, _) ->
    Format.fprintf ppf "%s" s
  | Ofp32 _ | Ofp64 _ ->
    invalid_arg "tried to emit a floating point literal in an operand"
  | Oah ->
    Format.fprintf ppf "ah"

let emit_tblentry (start : Label.t) ppf (dest : Label.t) =
  Format.fprintf ppf "  .long .L%a-.L%a\n"
    Int63.pp (dest :> Int63.t)
    Int63.pp (start :> Int63.t)

let emit_insn ppf : Insn.t -> unit = function
  | One (op, a) ->
    Format.fprintf ppf "  %a %a\n" Insn.pp_unop op emit_operand a
  | Two (op, a, b) ->
    Format.fprintf ppf "  %a %a, %a\n"
      Insn.pp_binop op emit_operand a emit_operand b
  | CDQ ->
    Format.fprintf ppf "  cdq\n"
  | CQO ->
    Format.fprintf ppf "  cqo\n"
  | CWD ->
    Format.fprintf ppf "  cwd\n"
  | IMUL3 (a, b, c) ->
    Format.fprintf ppf "  imul %a, %a, 0x%lx\n"
      emit_operand a emit_operand b c
  | Jcc (cc, l) ->
    Format.fprintf ppf "  j%a %a\n"
      Insn.pp_cc cc Int63.pp (l :> Int63.t)
  | JMP (Jind a) ->
    Format.fprintf ppf "  jmp %a\n" emit_operand a
  | JMP (Jlbl l) ->
    Format.fprintf ppf "  jmp .L%a\n" Int63.pp (l :> Int63.t)
  | RET ->
    Format.fprintf ppf "  ret\n"
  | UD2 ->
    Format.fprintf ppf "  ud2\n"
  | JMPtbl (l, ls) ->
    Format.fprintf ppf ".L%a:\n" Int63.pp (l :> Int63.t);
    List.iter ls ~f:(emit_tblentry l ppf)
