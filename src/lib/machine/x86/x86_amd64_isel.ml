module R = X86_amd64_common.Reg
module Rv = X86_amd64_common.Regvar

module Make(C : Context_intf.S) = struct
  open C.Syntax
  open X86_amd64_common.Insn

  let extend_flag_ty = function
    | `flag -> `i32
    | #Type.basic as t -> t

  let move dst ty (src : [Virtual.operand | `reg of R.t]) =
    let ty = extend_flag_ty ty in
    let dst = Oreg (dst, ty) in
    match ty, src with
    | #Type.imm, `int (i, _) ->
      !![MOV (dst, Oimm (Bv.to_int64 i))]
    | #Type.imm, `bool false ->
      !![XOR (dst, dst)]
    | #Type.imm, `bool true ->
      !![MOV (dst, Oimm 1L)]
    | #Type.imm, `sym (s, o) ->
      !![LEA (dst, Omem (Abd (Rv.reg `rip, Dsym (s, o))))]
    | #Type.imm, `var x ->
      !![MOV (dst, Oreg (Rv.var x, ty))]
    | #Type.imm, `reg (#R.gpr as r) ->
      !![MOV (dst, Oreg (Rv.reg r, ty))]
    | `f32, `float f ->
      !![MOVSS (dst, Ofp32 f)]
    | `f32, `var x ->
      !![MOVSS (dst, Oreg (Rv.var x, ty))]
    | `f32, `reg (#R.sse as r) ->
      !![MOVSS (dst, Oreg (Rv.reg r, ty))]
    | `f64, `double d ->
      !![MOVSD (dst, Ofp64 d)]
    | `f64, `var x ->
      !![MOVSD (dst, Oreg (Rv.var x, ty))]
    | `f64, `reg (#R.sse as r) ->
      !![MOVSD (dst, Oreg (Rv.reg r, ty))]
    | _, (#Virtual.operand as src) ->
      C.failf "In X86_amd64_isel.move: invalid type (%a) and operand (%a) combination"
        Type.pp_basic ty Virtual.pp_operand src ()
    | _, `reg r ->
      C.failf "In X86_amd64_isel.move: invalid type (%a) and register (%a) combination"
        Type.pp_basic ty R.pp r ()

  let rules = []
end
