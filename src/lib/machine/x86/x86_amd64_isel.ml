open Core

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
  let z = P.var "z"

  let yes = P.var "yes"
  let no = P.var "no"

  let label env x = match S.find env x with
    | Some (Label l) -> Some l
    | _ -> None

  let xor_gpr x xt =
    let x = Oreg (x, xt) in
    XOR (x, x)

  let move_x_y env =
    let*! x = S.find env "x" in
    let*! y = S.find env "y" in
    match x, y with
    | Regvar (x, _), Regvar (y, _) when Rv.equal x y -> !!![]
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

  let add_x_y_z env =
    let*! x = S.find env "x" in
    let*! y = S.find env "y" in
    let*! z = S.find env "z" in
    match x, y, z with
    | Regvar (x, (#Type.imm as xt)),
      Regvar (y, (#Type.imm as yt)),
      Imm (z, _) ->
      let z = Bv.to_int64 z in
      if Int64.(z >= 0L && z <= 0x7FFFFFFL) then
        let z = Int64.to_int32_trunc z in
        !!![LEA (Oreg (x, xt), Omem (Abd (y, Dimm z)))]
      else if Rv.equal x y then
        !!![ADD (Oreg (x, xt), Oimm z)]
      else
        !!![
          MOV (Oreg (x, xt), Oreg (y, yt));
          ADD (Oreg (x, xt), Oimm z);
        ]
    | _ -> !!None

  let sub_x_y_z env =
    let*! x = S.find env "x" in
    let*! y = S.find env "y" in
    let*! z = S.find env "z" in
    match x, y, z with
    | Regvar (x, (#Type.imm as xt)),
      Regvar (y, (#Type.imm as yt)),
      Imm (z, _) ->
      let z = Bv.to_int64 z in
      if Rv.equal x y then
        !!![SUB (Oreg (x, xt), Oimm z)]
      else
        !!![
          MOV (Oreg (x, xt), Oreg (y, yt));
          SUB (Oreg (x, xt), Oimm z);
        ]
    | _ -> !!None

  let jle_x_y env =
    let*! x = S.find env "x" in
    let*! y = S.find env "y" in
    let*! yes = label env "yes" in
    let*! no = label env "no" in
    match x, y with
    | Regvar (x, xt), Imm (y, _) -> !!![
        CMP (Oreg (x, xt), Oimm (Bv.to_int64 y));
        Jcc (Cle, yes);
        JMP (`lbl no);
      ]
    | _ -> !!None

  let ret_ _ = !!![RET]

  let rules = O.[
      move x (add `i32 y z) => add_x_y_z;
      move x (add `i64 y z) => add_x_y_z;
      move x (sub `i32 y z) => sub_x_y_z;
      move x (sub `i64 y z) => sub_x_y_z;
      move x y => move_x_y;

      (* jle *)
      br (le `i32 x y) yes no => jle_x_y;
      br (le `i64 x y) yes no => jle_x_y;

      (* ret *)
      ret => ret_;
    ]
end
