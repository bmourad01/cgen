(* The targets this case are the GNU and LLVM assemblers.

   Why do we use Intel syntax?

   1. Because it's the syntax described in the Intel and AMD manuals!
   2. Because it's prettier than AT&T syntax.
   3. Because you can go pound sand if you disagree!
*)

open Core
open Regular.Std
open X86_amd64_common

module Data = Virtual.Data

let label ppf (l : Label.t) =
  Format.fprintf ppf ".L%a" Int63.pp (l :> Int63.t)

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
  Format.fprintf ppf "%s:\n" name;
  Format.fprintf ppf "  endbr64\n"

let emit_blk ppf (l : Label.t) =
  Format.fprintf ppf "%a:\n" label l

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
  | Ab b ->
    Format.fprintf ppf "%a" rv b
  | Abd (b, d) when Int32.(d < 0l) ->
    Format.fprintf ppf "%a - 0x%lx" rv b (Int32.neg d)
  | Abd (b, d) ->
    Format.fprintf ppf "%a + 0x%lx" rv b d
  | Abis (b, i, s) ->
    Format.fprintf ppf "%a + %a*%a" rv b rv i Insn.pp_scale s
  | Aisd (i, s, d) when Int32.(d < 0l) ->
    Format.fprintf ppf "%a*%a - 0x%lx"
      rv i Insn.pp_scale s (Int32.neg d)
  | Aisd (i, s, d) ->
    Format.fprintf ppf "%a*%a + 0x%lx"
      rv i Insn.pp_scale s d
  | Abisd (b, i, s, d) when Int32.(d < 0l) ->
    Format.fprintf ppf "%a + %a*%a - 0x%lx"
      rv b rv i Insn.pp_scale s (Int32.neg d)
  | Abisd (b, i, s, d) ->
    Format.fprintf ppf "%a + %a*%a + 0x%lx"
      rv b rv i Insn.pp_scale s d
  | Asym (s, o) when o < 0 ->
    Format.fprintf ppf "rip + %s-%d" s (-o)
  | Asym (s, o) when o > 0 ->
    Format.fprintf ppf "rip + %s+%d" s o
  | Asym (s, _) ->
    Format.fprintf ppf "rip + %s" s
  | Albl (l, o) when o < 0 ->
    Format.fprintf ppf "rip + %a-%d" label l (-o)
  | Albl (l, o) when o > 0 ->
    Format.fprintf ppf "rip + %a+%d" label l o
  | Albl (l, _) ->
    Format.fprintf ppf "rip + %a" label l

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
  | Oah ->
    Format.fprintf ppf "ah"

let emit_tblentry (start : Label.t) ppf (dest : Label.t) =
  Format.fprintf ppf "  .long %a-%a\n" label dest label start

let emit_insn ppf (_l, i, s) =
  let s = Option.value s ~default:".text" in
  let op = emit_operand in
  match (i : Insn.t) with
  | One (o, a) ->
    Format.fprintf ppf "  %a %a\n" Insn.pp_unop o op a
  | Two (o, a, b) ->
    Format.fprintf ppf "  %a %a, %a\n"
      Insn.pp_binop o op a op b
  | CDQ ->
    Format.fprintf ppf "  cdq\n"
  | CQO ->
    Format.fprintf ppf "  cqo\n"
  | CWD ->
    Format.fprintf ppf "  cwd\n"
  | IMUL3 (a, b, c) ->
    Format.fprintf ppf "  imul %a, %a, 0x%lx\n"
      op a op b c
  | Jcc (cc, l) ->
    Format.fprintf ppf "  j%a %a\n"
      Insn.pp_cc cc label l
  | JMP (Jind a) ->
    Format.fprintf ppf "  jmp %a\n" op a
  | JMP (Jlbl l) ->
    Format.fprintf ppf "  jmp %a\n" label l
  | RET ->
    Format.fprintf ppf "  ret\n"
  | UD2 ->
    Format.fprintf ppf "  ud2\n"
  | LEAVE ->
    Format.fprintf ppf "  leave\n"
  | JMPtbl (l, ls) ->
    Format.fprintf ppf ".section .rodata\n.p2align 2\n%a:\n" label l;
    List.iter ls ~f:(emit_tblentry l ppf);
    Format.fprintf ppf ".section %s\n" s;
  | FP32 (l, f) ->
    Format.fprintf ppf ".section .rodata\n.p2align 2\n%a:\n  .float %s\n.section %s\n"
      label l (Float32.to_string f) s
  | FP64 (l, f) ->
    Format.fprintf ppf ".section .rodata\n.p2align 3\n%a:\n  .double %a\n.section %s\n"
      label l Float.pp f s

let emit_separator ppf () = Format.fprintf ppf "\n"
