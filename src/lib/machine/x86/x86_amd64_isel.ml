module R = X86_amd64_common.Reg
module Rv = X86_amd64_common.Regvar

module Make(C : Context_intf.S) = struct
  open C.Syntax
  open Isel_rewrite.Rule(C)
  open X86_amd64_common.Insn

  module P = Isel_rewrite.Pattern
  module S = Isel_rewrite.Subst
  module O = P.Op

  let (let*!) x f = match x with
    | Some x -> f x
    | None -> !!None

  let (!!!) x = !!(Some x)

  let x = P.var "x"
  let y = P.var "y"
  let sym = P.sym "sym"

  let xor_gpr x xt =
    let x = Oreg (x, xt) in
    XOR (x, x)

  let move_x_y env =
    let*! x = S.find env "x" in
    let*! y = S.find env "x" in
    match x, y with
    | Regvar (x, (#Type.imm as xt)), Regvar (y, (#Type.imm as yt)) ->
      !!![MOV (Oreg (x, xt), Oreg (y, yt))]
    | Regvar (x, (#Type.imm as xt)), Imm (y, _) when Bv.(y = zero) ->
      !!![xor_gpr x xt]
    | Regvar (x, (#Type.imm as xt)), Imm (y, _) ->
      !!![MOV (Oreg (x, xt), Oimm (Bv.to_int64 y))]
    | Regvar (x, (#Type.imm as xt)), Bool true ->
      !!![MOV (Oreg (x, xt), Oimm 1L)]
    | Regvar (x, (#Type.imm as xt)), Bool false ->
      !!![xor_gpr x xt]
    | Regvar (x, `i64), Sym (s, o) ->
      !!![LEA (Oreg (x, `i64), Omem (Abd (Rv.reg `rip, Dsym (s, o))))]
    | Regvar (x, `f32), Regvar (y, `f32) ->
      !!![MOVSS (Oreg (x, `f32), Oreg (y, `f32))]
    | Regvar (x, `f64), Regvar (y, `f64) ->
      !!![MOVSD (Oreg (x, `f64), Oreg (y, `f64))]
    | Regvar (x, `f32), Double d ->
      !!![MOVSD (Oreg (x, `f32), Ofp64 d)]
    | Regvar (x, `f32), Single s ->
      !!![MOVSS (Oreg (x, `f32), Ofp32 s)]
    | _ -> !!None

  let rules = O.[
      (* Generic move. *)
      move x y => move_x_y;
    ]
end
