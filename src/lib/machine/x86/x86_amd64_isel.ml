open Core

module R = X86_amd64_common.Reg
module Rv = X86_amd64_common.Regvar

let (>*) x f = List.bind x ~f

let bty ty = (ty :> Type.basic)
let mty ty = (ty :> X86_amd64_common.Insn.memty)

module Make(C : Context_intf.S) = struct
  open C.Syntax
  open Isel_rewrite.Rule(C)
  open X86_amd64_common.Insn

  module P = Isel_rewrite.Pattern
  module S = Isel_rewrite.Subst

  let x = P.var "x"
  let y = P.var "y"
  let z = P.var "z"
  let yes = P.var "yes"
  let no = P.var "no"

  let xor_gpr_self x ty =
    (* Shorter instruction encoding when we use the 32-bit register,
       which is implicitly zero-extended to 64 bits. *)
    let ty = match ty with
      | `i64 -> `i32
      | _ -> ty in
    let x = Oreg (x, ty) in
    XOR (x, x)

  let fits_int8 x =
    let open Int64 in
    x >= 0xFFFFFFFFFFFFFF80L &&
    x <= 0xFFL

  let fits_int32 x =
    let open Int64 in
    x >= 0xFFFFFFFF80000000L &&
    x <= 0xFFFFFFFFL

  let fits_int32_neg x =
    let open Int64 in
    x < 0L && x >= 0xFFFFFFFF80000000L

  let fits_int32_pos x =
    let open Int64 in
    x > 0L && x <= 0x7FFFFFFFL

  let can_lea_ty = function
    | `i16 | `i32 | `i64 -> true
    | _ -> false

  (* Rule callbacks. *)

  let nop _ = !!![]

  let move_rr_x_y env =
    let*! x, xt = S.regvar env "x" in
    let*! y, yt = S.regvar env "y" in
    if Rv.equal x y && Type.equal_basic xt yt then !!![]
    else match xt, yt with
      | (#Type.imm as xi), (#Type.imm as yi)
        when Type.sizeof_imm xi > Type.sizeof_imm yi ->
        (* Assume zero-extension is desired. *)
        !!![MOVZX (Oreg (x, xt), Oreg (y, yt))]
      | (#Type.imm as xi), (#Type.imm as yi)
        when Type.sizeof_imm xi < Type.sizeof_imm yi && Rv.equal x y ->
        !!![]
      | #Type.imm, #Type.imm ->
        (* Assume the width of the destination register. *)
        !!![MOV (Oreg (x, xt), Oreg (y, xt))]
      | `f32, `f32 ->
        !!![MOVSS (Oreg (x, xt), Oreg (y, yt))]
      | `f64, `f64 ->
        !!![MOVSD (Oreg (x, xt), Oreg (y, yt))]
      | _ -> !!None

  let move_ri_x_y env =
    let*! x, xt = S.regvar env "x" in
    let*! y, yt = S.imm env "y" in
    if Bv.(y = zero)
    then !!![xor_gpr_self x xt]
    else !!![MOV (Oreg (x, xt), Oimm (Bv.to_int64 y, yt))]

  let move_rb_x_y env =
    let*! x, xt = S.regvar env "x" in
    let*! xti = match xt with
      | #Type.imm as t -> Some t
      | _ -> None in
    let*! y = S.bool env "y" in
    if y then !!![MOV (Oreg (x, xt), Oimm (1L, xti))]
    else !!![xor_gpr_self x xt]

  let move_rsym_x_y env =
    let*! x, xt = S.regvar env "x" in
    let*! s, o = S.sym env "y" in
    let addr = Abd (Rv.reg `rip, Dsym (s, o)) in
    !!![LEA (Oreg (x, xt), Omem (addr, `i64))]

  let move_rf32_x_y env =
    let*! x, xt = S.regvar env "x" in
    let*! () = guard @@ Type.equal_basic xt `f32 in
    let*! s = S.single env "y" in
    !!![MOVSS (Oreg (x, xt), Ofp32 s)]

  let move_rf64_x_y env =
    let*! x, xt = S.regvar env "x" in
    let*! () = guard @@ Type.equal_basic xt `f64 in
    let*! d = S.double env "y" in
    !!![MOVSS (Oreg (x, xt), Ofp64 d)]

  let add_rr_x_y_z env =
    let*! x, xt = S.regvar env "x" in
    let*! y, yt = S.regvar env "y" in
    let*! z, zt = S.regvar env "z" in
    let*! () = guard @@ Type.equal_basic xt yt in
    let*! () = guard @@ Type.equal_basic xt zt in
    if not (Rv.equal x y) && can_lea_ty xt then
      !!![LEA (Oreg (x, xt), Omem (Abi (y, z), `i64))]
    else
      !!![
        MOV (Oreg (x, xt), Oreg (y, yt));
        ADD (Oreg (x, xt), Oreg (z, zt));
      ]

  let add_mul_rr_scale_x_y_z s env =
    let*! x, xt = S.regvar env "x" in
    let*! y, _ = S.regvar env "y" in
    let*! z, _ = S.regvar env "z" in
    let*! () = guard @@ can_lea_ty xt in
    !!![LEA (Oreg (x, xt), Omem (Abis (y, z, s), `i64))]

  let add_ri_x_y_z env =
    let*! x, xt = S.regvar env "x" in
    let*! y, yt = S.regvar env "y" in
    let*! () = guard @@ Type.equal_basic xt yt in
    let*! z, zt = S.imm env "z" in
    let z = Bv.to_int64 z in
    if Int64.(z = 0L) then
      !!![MOV (Oreg (x, xt), Oreg (y, yt))]
    else if not (Rv.equal x y) && fits_int32_pos z && can_lea_ty xt then
      let z = Int64.to_int32_trunc z in
      !!![LEA (Oreg (x, xt), Omem (Abd (y, Dimm z), `i64))]
    else if Rv.equal x y then
      !!![ADD (Oreg (x, xt), Oimm (z, zt))]
    else
      !!![
        MOV (Oreg (x, xt), Oreg (y, yt));
        ADD (Oreg (x, xt), Oimm (z, zt));
      ]

  let sub_rr_x_y_z env =
    let*! x, xt = S.regvar env "x" in
    let*! y, yt = S.regvar env "y" in
    let*! z, zt = S.regvar env "z" in
    let*! () = guard @@ Type.equal_basic xt yt in
    let*! () = guard @@ Type.equal_basic xt zt in !!![
      MOV (Oreg (x, xt), Oreg (y, yt));
      SUB (Oreg (x, xt), Oreg (z, zt));
    ]

  let sub_ri_x_y_z env =
    let*! x, xt = S.regvar env "x" in
    let*! y, yt = S.regvar env "y" in
    let*! () = guard @@ Type.equal_basic xt yt in
    let*! z, zt = S.imm env "z" in
    let z = Bv.to_int64 z in
    let nz = Int64.neg z in
    if Int64.(z = 0L) then
      !!![MOV (Oreg (x, xt), Oreg (y, yt))]
    else if not (Rv.equal x y) && fits_int32_neg nz && can_lea_ty xt then
      let z = Int64.to_int32_trunc nz in
      !!![LEA (Oreg (x, xt), Omem (Abd (y, Dimm z), `i64))]
    else if Rv.equal x y then
      !!![SUB (Oreg (x, xt), Oimm (z, zt))]
    else
      !!![
        MOV (Oreg (x, xt), Oreg (y, yt));
        SUB (Oreg (x, xt), Oimm (z, zt));
      ]

  let and_ri_x_y_z env =
    let*! x, xt = S.regvar env "x" in
    let*! y, yt = S.regvar env "y" in
    let*! z, zt = S.imm env "z" in !!![
      MOV (Oreg (x, xt) , Oreg (y, yt));
      AND (Oreg (x, xt), Oimm (Bv.to_int64 z, zt));
    ]

  let jmp_lbl_x env =
    let*! x = S.label env "x" in
    !!![JMP (Jlbl x)]

  let jmp_sym_x env =
    let*! s, o = S.sym env "x" in
    !!![JMP (Jind (Osym (s, o), Label.Set.empty))]

  let jcc_r_zero_x ?(neg = false) env =
    let*! x, xt = S.regvar env "x" in
    let*! yes = S.label env "yes" in
    let*! no = S.label env "no" in
    let cc = if neg then Cne else Ce in !!![
      TEST_ (Oreg (x, xt), Oreg (x, xt));
      Jcc (cc, yes);
      JMP (Jlbl no);
    ]

  let jcc_rr_x_y cc env =
    let*! x, xt = S.regvar env "x" in
    let*! y, yt = S.regvar env "y" in
    let*! yes = S.label env "yes" in
    let*! no = S.label env "no" in !!![
      CMP (Oreg (x, xt), Oreg (y, yt));
      Jcc (cc, yes);
      JMP (Jlbl no);
    ]

  let jcc_rr_f32_x_y cc env =
    let*! x, xt = S.regvar env "x" in
    let*! y, yt = S.regvar env "y" in
    let*! yes = S.label env "yes" in
    let*! no = S.label env "no" in !!![
      UCOMISS (Oreg (x, xt), Oreg (y, yt));
      Jcc (cc, yes);
      JMP (Jlbl no);
    ]

  let jcc_rr_f64_x_y cc env =
    let*! x, xt = S.regvar env "x" in
    let*! y, yt = S.regvar env "y" in
    let*! yes = S.label env "yes" in
    let*! no = S.label env "no" in !!![
      UCOMISD (Oreg (x, xt), Oreg (y, yt));
      Jcc (cc, yes);
      JMP (Jlbl no);
    ]

  let jcc_ri_x_y cc env =
    let*! x, xt = S.regvar env "x" in
    let*! y, yt = S.imm env "y" in
    let*! yes = S.label env "yes" in
    let*! no = S.label env "no" in
    let y = Bv.to_int64 y in
    if fits_int32 y then !!![
        CMP (Oreg (x, xt), Oimm (y, yt));
        Jcc (cc, yes);
        JMP (Jlbl no);
      ]
    else
      let*! () = guard @@ Type.equal_basic xt `i64 in
      let+ y' = C.Var.fresh >>| Rv.var in
      Some [
        MOV (Oreg (y', `i64), Oimm (y, yt));
        CMP (Oreg (x, xt), Oreg (y', `i64));
        Jcc (cc, yes);
        JMP (Jlbl no);
      ]

  (* Default to 8-bit *)
  let setcc_r_zero_x_y ?(neg = false) env =
    let*! x, _ = S.regvar env "x" in
    let*! y, yt = S.regvar env "y" in
    let cc = if neg then Cne else Ce in !!![
      TEST_ (Oreg (y, yt), Oreg (y, yt));
      SETcc (cc, Oreg (x, `i8));
    ]

  (* Default to 8-bit *)
  let setcc_rr_x_y_z cc env =
    let*! x, _ = S.regvar env "x" in
    let*! y, yt = S.regvar env "y" in
    let*! z, zt = S.regvar env "z" in !!![
      CMP (Oreg (y, yt), Oreg (z, zt));
      SETcc (cc, Oreg (x, `i8));
    ]

  (* Default to 8-bit *)
  let setcc_rr_f32_x_y_z cc env =
    let*! x, _ = S.regvar env "x" in
    let*! y, yt = S.regvar env "y" in
    let*! z, zt = S.regvar env "z" in !!![
      UCOMISS (Oreg (y, yt), Oreg (z, zt));
      SETcc (cc, Oreg (x, `i8));
    ]

  (* Default to 8-bit *)
  let setcc_rr_f64_x_y_z cc env =
    let*! x, _ = S.regvar env "x" in
    let*! y, yt = S.regvar env "y" in
    let*! z, zt = S.regvar env "z" in !!![
      UCOMISD (Oreg (y, yt), Oreg (z, zt));
      SETcc (cc, Oreg (x, `i8));
    ]

  (* Default to 8-bit *)
  let setcc_ri_x_y_z cc env =
    let*! x, _ = S.regvar env "x" in
    let*! y, yt = S.regvar env "y" in
    let*! z, zt = S.imm env "z" in
    let z = Bv.to_int64 z in
    if fits_int32 z then !!![
        CMP (Oreg (y, yt), Oimm (z, zt));
        SETcc (cc, Oreg (x, `i8));
      ]
    else
      let* tmp = C.Var.fresh >>| Rv.var in !!![
        MOV (Oreg (tmp, `i64), Oimm (z, zt));
        CMP (Oreg (y, yt), Oreg (tmp, `i64));
        SETcc (cc, Oreg (x, `i8));
      ]

  let load_rri_add_x_y_z env =
    let*! x, xt = S.regvar env "x" in
    let*! y, _ = S.regvar env "y" in
    let*! z, _ = S.imm env "z" in
    let z = Bv.to_int64 z in
    let*! () = guard @@ fits_int32 z in
    let z = Int64.to_int32_trunc z in !!![
      MOV (Oreg (x, xt), Omem (Abd (y, Dimm z), mty xt));
    ]

  let load_rr_x_y env =
    let*! x, xt = S.regvar env "x" in
    let*! y, _ = S.regvar env "y" in !!![
      MOV (Oreg (x, xt), Omem (Ab y, mty xt));
    ]

  let store_rr_x_y env =
    let*! x, xt = S.regvar env "x" in
    let*! y, _ = S.regvar env "y" in !!![
      MOV (Omem (Ab y, mty xt), Oreg (x, xt));
    ]

  let store_ri_x_y env =
    let*! x, xt = S.imm env "x" in
    let*! y, _ = S.regvar env "y" in !!![
      MOV (Omem (Ab y, mty xt), Oimm (Bv.to_int64 x, xt));
    ]

  let store_rri_add_x_y_z env =
    let*! x, xt = S.regvar env "x" in
    let*! y, _ = S.regvar env "y" in
    let*! z, _ = S.imm env "z" in
    let z = Bv.to_int64 z in
    let*! () = guard @@ fits_int32 z in
    let z = Int64.to_int32_trunc z in !!![
      MOV (Omem (Abd (y, Dimm z), mty xt), Oreg (x, xt));
    ]

  let store_iri_add_x_y_z env =
    let*! x, xt = S.imm env "x" in
    let*! y, _ = S.regvar env "y" in
    let*! z, _ = S.imm env "z" in
    let z = Bv.to_int64 z in
    let*! () = guard @@ fits_int32 z in
    let z = Int64.to_int32_trunc z in
    let x = Bv.to_int64 x in !!![
      MOV (Omem (Abd (y, Dimm z), mty xt), Oimm (x, xt));
    ]

  let store_rsym_x_y env =
    let*! s, o = S.sym env "x" in
    let*! y, yt = S.regvar env "y" in
    let addr = Abd (Rv.reg `rip, Dsym (s, o)) in
    let* x = C.Var.fresh >>| Rv.var in !!![
      LEA (Oreg (x, `i64), Omem (addr, `i64));
      MOV (Omem (Ab y, mty yt), Oreg (x, yt))
    ]

  let store_symr_x_y env =
    let*! x, xt = S.regvar env "x" in
    let*! s, o = S.sym env "y" in
    let addr = Abd (Rv.reg `rip, Dsym (s, o)) in !!![
      MOV (Omem (addr, mty xt), Oreg (x, xt));
    ]

  let store_v_rr_x_y env =
    let*! x = S.regvar_v env "x" in
    let*! y, _ = S.regvar env "y" in !!![
      MOVDQA (Omem (Ab y, `v128), Oregv x);
    ]

  let store_v_rri_add_x_y_z env =
    let*! x = S.regvar_v env "x" in
    let*! y, _ = S.regvar env "y" in
    let*! z, _ = S.imm env "z" in
    let z = Bv.to_int64 z in
    let*! () = guard @@ fits_int32 z in
    let z = Int64.to_int32_trunc z in !!![
      MOVDQA (Omem (Abd (y, Dimm z), `v128), Oregv x);
    ]

  let mul_lea_ri_x_y s env =
    let*! x, xt = S.regvar env "x" in
    let*! y, _ = S.regvar env "y" in
    let*! () = guard @@ can_lea_ty xt in
    !!![LEA (Oreg (x, xt), Omem (Aisd (y, s, Dimm 0l), `i64))]

  let imul_rr_x_y_z env =
    let*! x, xt = S.regvar env "x" in
    let*! y, yt = S.regvar env "y" in
    let*! z, zt = S.regvar env "z" in !!![
      MOV (Oreg (x, xt), Oreg (y, yt));
      IMUL2 (Oreg (x, xt), Oreg (z, zt));
    ]

  let imul_ri_x_y_z env =
    let*! x, xt = S.regvar env "x" in
    let*! y, yt = S.regvar env "y" in
    let*! z, zt = S.imm env "z" in
    let z = Bv.to_int64 z in
    if fits_int32 z then !!![
        IMUL3 (Oreg (x, xt), Oreg (y, yt), Int64.to_int32_trunc z);
      ]
    else
      let* z' = C.Var.fresh >>| Rv.var in !!![
        MOV (Oreg (z', xt), Oimm (z, zt));
        MOV (Oreg (x, xt), Oreg (y, yt));
        IMUL2 (Oreg (x, xt), Oreg (z', xt));
      ]

  let imul_ri_high_x_y_z env =
    let*! x, xt = S.regvar env "x" in
    let*! y, yt = S.regvar env "y" in
    let*! z, zt = S.imm env "z" in
    let z = Bv.to_int64 z in
    let rax = Rv.reg `rax in
    let rdx = Rv.reg `rdx in !!![
      MOV (Oreg (rax, bty zt), Oimm (z, zt));
      IMUL1 (Oreg (y, yt));
      MOV (Oreg (x, xt), Oreg (rdx, xt));
    ]

  let imul_rr_high_x_y_z env =
    let*! x, xt = S.regvar env "x" in
    let*! y, yt = S.regvar env "y" in
    let*! z, zt = S.regvar env "z" in
    let rax = Rv.reg `rax in
    let rdx = Rv.reg `rdx in !!![
      MOV (Oreg (rax, yt), Oreg (y, yt));
      IMUL1 (Oreg (z, zt));
      MOV (Oreg (x, xt), Oreg (rdx, xt));
    ]

  let mul_ri_high_x_y_z env =
    let*! x, xt = S.regvar env "x" in
    let*! y, yt = S.regvar env "y" in
    let*! z, zt = S.imm env "z" in
    let z = Bv.to_int64 z in
    let rax = Rv.reg `rax in
    let rdx = Rv.reg `rdx in !!![
      MOV (Oreg (rax, bty zt), Oimm (z, zt));
      MUL (Oreg (y, yt));
      MOV (Oreg (x, xt), Oreg (rdx, xt));
    ]

  let mul_rr_high_x_y_z env =
    let*! x, xt = S.regvar env "x" in
    let*! y, yt = S.regvar env "y" in
    let*! z, zt = S.regvar env "z" in
    let rax = Rv.reg `rax in
    let rdx = Rv.reg `rdx in !!![
      MOV (Oreg (rax, yt), Oreg (y, yt));
      MUL (Oreg (z, zt));
      MOV (Oreg (x, xt), Oreg (rdx, xt));
    ]

  let idiv_rem_rr_x_y_z env =
    let*! x, xt = S.regvar env "x" in
    let*! y, yt = S.regvar env "y" in
    let*! z, zt = S.regvar env "z" in
    let rax = Rv.reg `rax in
    let rdx = Rv.reg `rdx in !!![
      MOV (Oreg (rax, yt), Oreg (y, yt));
      IDIV (Oreg (z, zt));
      MOV (Oreg (x, xt), Oreg (rdx, xt));
    ]

  let lsl_rr_x_y_z env =
    let*! x, xt = S.regvar env "x" in
    let*! y, yt = S.regvar env "y" in
    let*! z, _ = S.regvar env "z" in
    let rcx = Rv.reg `rcx in !!![
      MOV (Oreg (x, xt), Oreg (y, yt));
      MOV (Oreg (rcx, `i8), Oreg (z, `i8));
      SHL (Oreg (x, xt), Oreg (rcx, `i8));
    ]

  (* The shift value is ANDed with 0x3F or 0x1F by the hardware. *)
  let lsl_ri_x_y_z env =
    let*! x, xt = S.regvar env "x" in
    let*! y, yt = S.regvar env "y" in
    let*! z, _ = S.imm env "z" in
    let z = Bv.to_int64 z in !!![
      MOV (Oreg (x, xt), Oreg (y, yt));
      SHL (Oreg (x, xt), Oimm (Int64.(z land 0xFFL), `i8));
    ]

  let lsr_rr_x_y_z env =
    let*! x, xt = S.regvar env "x" in
    let*! y, yt = S.regvar env "y" in
    let*! z, _ = S.regvar env "z" in
    let rcx = Rv.reg `rcx in !!![
      MOV (Oreg (x, xt), Oreg (y, yt));
      MOV (Oreg (rcx, `i8), Oreg (z, `i8));
      SHR (Oreg (x, xt), Oreg (rcx, `i8));
    ]

  (* The shift value is ANDed with 0x3F or 0x1F by the hardware. *)
  let lsr_ri_x_y_z env =
    let*! x, xt = S.regvar env "x" in
    let*! y, yt = S.regvar env "y" in
    let*! z, _ = S.imm env "z" in
    let z = Bv.to_int64 z in !!![
      MOV (Oreg (x, xt), Oreg (y, yt));
      SHR (Oreg (x, xt), Oimm (Int64.(z land 0xFFL), `i8));
    ]

  let asr_rr_x_y_z env =
    let*! x, xt = S.regvar env "x" in
    let*! y, yt = S.regvar env "y" in
    let*! z, _ = S.regvar env "z" in
    let rcx = Rv.reg `rcx in !!![
      MOV (Oreg (x, xt), Oreg (y, yt));
      MOV (Oreg (rcx, `i8), Oreg (z, `i8));
      SAR (Oreg (x, xt), Oreg (rcx, `i8));
    ]

  (* The shift value is ANDed with 0x3F or 0x1F by the hardware. *)
  let asr_ri_x_y_z env =
    let*! x, xt = S.regvar env "x" in
    let*! y, yt = S.regvar env "y" in
    let*! z, _ = S.imm env "z" in
    let z = Bv.to_int64 z in !!![
      MOV (Oreg (x, xt), Oreg (y, yt));
      SAR (Oreg (x, xt), Oimm (Int64.(z land 0xFFL), `i8));
    ]

  let sext_rr_x_y env =
    let*! x, xt = S.regvar env "x" in
    let*! y, yt = S.regvar env "y" in
    match xt, yt with
    | `i64, `i32 ->
      !!![MOVSXD (Oreg (x, xt), Oreg (y, yt))]
    | (#Type.imm as xi), (#Type.imm as yi)
      when Type.sizeof_imm xi > Type.sizeof_imm yi ->
      !!![MOVSX (Oreg (x, xt), Oreg (y, yt))]
    | #Type.imm, #Type.imm ->
      (* Assume the width of the destination. *)
      !!![MOV (Oreg (x, xt), Oreg (y, xt))]
    | _ -> !!None

  let sext_ri_x_y env =
    let*! x, xt = S.regvar env "x" in
    match xt with
    | #Type.fp -> !!None
    | #Type.imm as xt' ->
      let*! y, yt = S.imm env "y" in
      match Virtual.Eval.unop_int (`sext xt') y yt with
      | Some `int (y, _) ->
        !!![MOV (Oreg (x, xt), Oimm (Bv.to_int64 y, xt'))]
      | _ -> !!None

  let call_sym_x env =
    let*! s, o = S.sym env "x" in
    !!![CALL (Osym (s, o))]

  open P.Op

  (* Re-used groups of callbacks. *)
  module Group = struct
    let add = [
      add_rr_x_y_z;
      add_ri_x_y_z;
    ]

    let sub = [
      sub_rr_x_y_z;
      sub_ri_x_y_z;
    ]

    let and_ = [
      and_ri_x_y_z;
    ]

    let lsl_ = [
      lsl_rr_x_y_z;
      lsl_ri_x_y_z;
    ]

    let lsr_ = [
      lsr_rr_x_y_z;
      lsr_ri_x_y_z;
    ]

    let asr_ = [
      asr_rr_x_y_z;
      asr_ri_x_y_z;
    ]

    let mul = [
      imul_rr_x_y_z;
      imul_ri_x_y_z;
    ]

    let mulh = [
      imul_rr_high_x_y_z;
      imul_ri_high_x_y_z;
    ]

    let umulh = [
      mul_rr_high_x_y_z;
      mul_ri_high_x_y_z;
    ]

    let rem = [
      idiv_rem_rr_x_y_z;
    ]

    let setcc cc = [
      setcc_rr_x_y_z cc;
      setcc_ri_x_y_z cc;
    ]

    let setcc_f32 cc = [
      setcc_rr_f32_x_y_z cc;
    ]

    let setcc_f64 cc = [
      setcc_rr_f64_x_y_z cc;
    ]

    let load = [
      load_rr_x_y;
    ]

    let move_ri = [
      move_rr_x_y;
      move_ri_x_y;
    ]

    let move = move_ri @ [
        move_rb_x_y;
        move_rsym_x_y;
        move_rf32_x_y;
        move_rf64_x_y;
      ]

    let sext = [
      sext_rr_x_y;
      sext_ri_x_y;
    ]

    let zext = [
      move_rr_x_y;
      move_ri_x_y;
    ]

    let store_add = [
      store_rri_add_x_y_z;
      store_iri_add_x_y_z;
    ]

    let store = [
      store_rr_x_y;
      store_ri_x_y;
      store_rsym_x_y;
      store_symr_x_y;
    ]

    let store_vec_add = [
      store_v_rri_add_x_y_z;
    ]

    let store_vec_basic = [
      store_v_rr_x_y;
    ]

    let jmp = [
      jmp_lbl_x;
      jmp_sym_x;
    ]

    let br_icmp cc = [
      jcc_rr_x_y cc;
      jcc_ri_x_y cc;
    ]

    let br_fcmp32 cc = [
      jcc_rr_f32_x_y cc;
    ]

    let br_fcmp64 cc = [
      jcc_rr_f64_x_y cc;
    ]

    let call = [
      call_sym_x;
    ]
  end

  (* The rules themselves. *)
  module Rules = struct
    (* No-op when moving to self. *)
    let move_nop = [
      move x x => nop;
    ]

    (* x = add y (mul z i) => lea x, [y+z*i]

       where i \in {1,2,4,8}

       x = add y (lsl z i) => lea x, [y+z*(1<<i)]

       where i \in {0,1,2,3}
    *)
    let add_mul_lea =
      [`i16, i16 0,  i16 1,  i16 2,  i16 3,  i16 4,  i16 8;
       `i32, i32 0l, i32 1l, i32 2l, i32 3l, i32 4l, i32 8l;
       `i64, i64 0L, i64 1L, i64 2L, i64 3L, i64 4L, i64 8L;
      ] >* fun (ty, zero, one, two, three, four, eight) ->
        let ty' = bty ty in [
          (* x = add (mul z i) y *)
          move x (add ty' y (mul ty' z one)) => add_mul_rr_scale_x_y_z 1;
          move x (add ty' y (mul ty' z two)) => add_mul_rr_scale_x_y_z 2;
          move x (add ty' y (mul ty' z four)) => add_mul_rr_scale_x_y_z 4;
          move x (add ty' y (mul ty' z eight)) => add_mul_rr_scale_x_y_z 8;
          (* x = add (mul z i) y *)
          move x (add ty' (mul ty' z one) y) => add_mul_rr_scale_x_y_z 1;
          move x (add ty' (mul ty' z two) y) => add_mul_rr_scale_x_y_z 2;
          move x (add ty' (mul ty' z four) y) => add_mul_rr_scale_x_y_z 4;
          move x (add ty' (mul ty' z eight) y) => add_mul_rr_scale_x_y_z 8;
          (* x = add y, (lsl z i) *)
          move x (add ty' y (lsl_ ty z zero)) => add_mul_rr_scale_x_y_z 1;
          move x (add ty' y (lsl_ ty z one)) => add_mul_rr_scale_x_y_z 2;
          move x (add ty' y (lsl_ ty z two)) => add_mul_rr_scale_x_y_z 4;
          move x (add ty' y (lsl_ ty z three)) => add_mul_rr_scale_x_y_z 8;
          (* x = add (lsl z i) y *)
          move x (add ty' (lsl_ ty z zero) y) => add_mul_rr_scale_x_y_z 1;
          move x (add ty' (lsl_ ty z one) y) => add_mul_rr_scale_x_y_z 2;
          move x (add ty' (lsl_ ty z two) y) => add_mul_rr_scale_x_y_z 4;
          move x (add ty' (lsl_ ty z three) y) => add_mul_rr_scale_x_y_z 8;
        ]

    (* x = add y, z *)
    let add_basic = [
      move x (add `i8 y z) =>* Group.add;
      move x (add `i16 y z) =>* Group.add;
      move x (add `i32 y z) =>* Group.add;
      move x (add `i64 y z) =>* Group.add;
    ]

    (* x = sub y z *)
    let sub_basic = [
      move x (sub `i8 y z) =>* Group.sub;
      move x (sub `i16 y z) =>* Group.sub;
      move x (sub `i32 y z) =>* Group.sub;
      move x (sub `i64 y z) =>* Group.sub;
    ]

    (* x = and y, z *)
    let and_basic = [
      move x (and_ `i8 y z) =>* Group.and_;
      move x (and_ `i16 y z) =>* Group.and_;
      move x (and_ `i32 y z) =>* Group.and_;
      move x (and_ `i64 y z) =>* Group.and_;
    ]

    (* x = lsl y, z *)
    let lsl_basic = [
      move x (lsl_ `i8 y z) =>* Group.lsl_;
      move x (lsl_ `i16 y z) =>* Group.lsl_;
      move x (lsl_ `i32 y z) =>* Group.lsl_;
      move x (lsl_ `i64 y z) =>* Group.lsl_;
    ]

    (* x = lsr y, z *)
    let lsr_basic = [
      move x (lsr_ `i8 y z) =>* Group.lsr_;
      move x (lsr_ `i16 y z) =>* Group.lsr_;
      move x (lsr_ `i32 y z) =>* Group.lsr_;
      move x (lsr_ `i64 y z) =>* Group.lsr_;
    ]

    (* x = asr y, z *)
    let asr_basic = [
      move x (asr_ `i8 y z) =>* Group.asr_;
      move x (asr_ `i16 y z) =>* Group.asr_;
      move x (asr_ `i32 y z) =>* Group.asr_;
      move x (asr_ `i64 y z) =>* Group.asr_;
    ]

    (*  x = mul y i => lea x, [y*i]

        where i \in {1,2,4,8}
    *)
    let mul_lea =
      [`i16, i16 1,  i16 2,  i16 4,  i16 8;
       `i32, i32 1l, i32 2l, i32 4l, i32 8l;
       `i64, i64 1L, i64 2L, i64 4L, i64 8L;
      ] >* fun (ty, one, two, four, eight) -> [
          (* x = mul y i *)
          move x (mul ty y one) => move_rr_x_y;
          move x (mul ty y two) => mul_lea_ri_x_y 2;
          move x (mul ty y four) => mul_lea_ri_x_y 4;
          move x (mul ty y eight) => mul_lea_ri_x_y 8;
          (* x = mul i y *)
          move x (mul ty one y) => move_rr_x_y;
          move x (mul ty two y) => mul_lea_ri_x_y 2;
          move x (mul ty four y) => mul_lea_ri_x_y 4;
          move x (mul ty eight y) => mul_lea_ri_x_y 8;
        ]

    (* x = mul y, z *)
    let mul_basic = [
      move x (mul `i32 y z) =>* Group.mul;
      move x (mul `i64 y z) =>* Group.mul;
    ]

    (* x = mulh y, z *)
    let mulh_basic = [
      move x (mulh `i32 y z) =>* Group.mulh;
      move x (mulh `i64 y z) =>* Group.mulh;
    ]

    (* x = umulh y, z *)
    let umulh_basic = [
      move x (umulh `i32 y z) =>* Group.umulh;
      move x (umulh `i64 y z) =>* Group.umulh;
    ]

    (* x = rem y, z *)
    let rem_basic = [
      move x (rem `i32 y z) =>* Group.rem;
    ]

    (* x = y == 0
       x = y != 0
    *)
    let setcc_zero =
      [`i8,  i8 0;
       `i16, i16 0;
       `i32, i32 0l;
       `i64, i64 0L;
      ] >* fun (ty, zero) -> [
          move x (eq ty y zero) => setcc_r_zero_x_y; (* x = y == 0 *)
          move x (eq ty zero y) => setcc_r_zero_x_y; (* x = 0 == y *)
          move x (ne ty y zero) => setcc_r_zero_x_y; (* x = y != 0 *)
          move x (ne ty zero y) => setcc_r_zero_x_y; (* x = 0 != y *)
        ]

    (* x = cmp y, z *)
    let setcc_ibasic =
      [`i8; `i16; `i32; `i64] >* fun ty ->
        let ty' = bty ty in [
          (* Equality *)
          move x (eq ty' y z) =>* Group.setcc Ce;
          move x (ne ty' y z) =>* Group.setcc Cne;
          (* Unsigned *)
          move x (lt ty' y z) =>* Group.setcc Cb;
          move x (le ty' y z) =>* Group.setcc Cbe;
          move x (gt ty' y z) =>* Group.setcc Ca;
          move x (ge ty' y z) =>* Group.setcc Cae;
          (* Signed *)
          move x (slt ty y z) =>* Group.setcc Cl;
          move x (sle ty y z) =>* Group.setcc Cle;
          move x (sgt ty y z) =>* Group.setcc Cg;
          move x (sge ty y z) =>* Group.setcc Cge;
        ]

    (* x = fcmp y, z *)
    let setcc_fbasic =
      [`f32, Group.setcc_f32;
       `f64, Group.setcc_f64
      ] >* fun (ty, f) ->
        let ty' = bty ty in [
          (* Equality *)
          move x (eq ty' y z) =>* f Ce;
          move x (ne ty' y z) =>* f Cne;
          (* Comparison *)
          move x (lt ty' y z) =>* f Cb;
          move x (le ty' y z) =>* f Cbe;
          move x (gt ty' y z) =>* f Ca;
          move x (ge ty' y z) =>* f Cae;
          (* Ordering *)
          move x (uo ty y z) =>* f Cp;
          move x (o ty y z) =>* f Cnp;
        ]

    (* x = load (add y, z) *)
    let load_add = [
      move x (load `i32 (add `i64 y z)) => load_rri_add_x_y_z;
      move x (load `i64 (add `i64 y z)) => load_rri_add_x_y_z;
    ]

    (* x = load y *)
    let load_basic = [
      move x (load `i32 y) =>* Group.load;
      move x (load `i64 y) =>* Group.load;
    ]

    (* x = sext y *)
    let sext_basic = [
      move x (sext `i8 y) =>* Group.move_ri;
      move x (sext `i16 y) =>* Group.sext;
      move x (sext `i32 y) =>* Group.sext;
      move x (sext `i64 y) =>* Group.sext;
    ]

    (* x = zext y *)
    let zext_basic = [
      move x (zext `i8 y) =>* Group.move_ri;
      move x (zext `i16 y) =>* Group.zext;
      move x (zext `i32 y) =>* Group.zext;
      move x (zext `i64 y) =>* Group.zext;
    ]

    (* x = flag y

       This ends up being just a move. We handle the cases that
       bind boolean-typed variables directly.
    *)
    let flag_basic =
      [`i8; `i16; `i32; `i64] >* fun ty -> [
          move x (flag ty y) =>* [
            move_rr_x_y;
            move_rb_x_y;
          ]
        ]

    (* x = y *)
    let move_basic = [
      move x y =>* Group.move;
    ]

    (* store x, xmmword ptr [y+z] *)
    let store_vec_add = [
      store `v128 x (add `i64 y z) =>* Group.store_vec_add;
    ]

    (* store x, xmmword ptr [y] *)
    let store_vec_basic = [
      store `v128 x y =>* Group.store_vec_basic;
    ]

    (* store x, [y + z] *)
    let store_add = [
      store `i32 x (add `i64 y z) =>* Group.store_add;
      store `i64 x (add `i64 y z) =>* Group.store_add;
    ]

    (* store x, [y] *)
    let store_basic = [
      store `i32 x y =>* Group.store;
      store `i64 x y =>* Group.store;
    ]

    (* jmp x *)
    let jmp_basic = [
      jmp x =>* Group.jmp;
    ]

    (* br (x == 0), yes, no
       br (x != 0), yes, no
    *)
    let br_zero =
      [`i8,  i8 0;
       `i16, i16 0;
       `i32, i32 0l;
       `i64, i64 0L;
      ] >* fun (ty, zero) -> [
          br (eq ty x zero) yes no => jcc_r_zero_x;
          br (eq ty zero x) yes no => jcc_r_zero_x;
          br (ne ty x zero) yes no => jcc_r_zero_x ~neg:true;
          br (ne ty zero x) yes no => jcc_r_zero_x ~neg:true;
        ]

    (* br (icmp x, y), yes, no *)
    let br_icmp =
      [`i8; `i16; `i32; `i64] >* fun ty ->
        let ty' = bty ty in [
          (* Equality *)
          br (eq ty' x y) yes no =>* Group.br_icmp Ce;
          br (ne ty' x y) yes no =>* Group.br_icmp Cne;
          (* Unsigned *)
          br (lt ty' x y) yes no =>* Group.br_icmp Cb;
          br (le ty' x y) yes no =>* Group.br_icmp Cbe;
          br (gt ty' x y) yes no =>* Group.br_icmp Ca;
          br (ge ty' x y) yes no =>* Group.br_icmp Cae;
          (* Signed *)
          br (slt ty x y) yes no =>* Group.br_icmp Cl;
          br (sle ty x y) yes no =>* Group.br_icmp Cle;
          br (sgt ty x y) yes no =>* Group.br_icmp Cg;
          br (sge ty x y) yes no =>* Group.br_icmp Cge;
        ]

    let br_fcmp =
      [ `f32, Group.br_fcmp32;
        `f64, Group.br_fcmp64;
      ] >* fun (ty, f) ->
        let ty' = bty ty in [
          (* Equality *)
          br (eq ty' x y) yes no =>* f Ce;
          br (ne ty' x y) yes no =>* f Cne;
          (* Comparison *)
          br (lt ty' x y) yes no =>* f Cb;
          br (le ty' x y) yes no =>* f Cbe;
          br (gt ty' x y) yes no =>* f Ca;
          br (ge ty' x y) yes no =>* f Cae;
          (* Ordering *)
          br (uo ty x y) yes no =>* f Cp;
          br (o ty x y) yes no =>* f Cnp;
        ]

    (* call x *)
    let call_basic = [
      call x =>* Group.call;
    ]

    (* hlt *)
    let hlt = [
      hlt => (fun _ -> !!![UD2]);
    ]

    (* ret *)
    let ret = [
      ret => (fun _ -> !!![RET]);
    ]
  end

  let rules =
    let open Rules in
    move_nop @
    add_mul_lea @
    add_basic @
    sub_basic @
    and_basic @
    lsl_basic @
    lsr_basic @
    asr_basic @
    mul_lea @
    mul_basic @
    mulh_basic @
    umulh_basic @
    rem_basic @
    setcc_zero @
    setcc_ibasic @
    setcc_fbasic @
    load_add @
    load_basic @
    sext_basic @
    zext_basic @
    flag_basic @
    move_basic @
    store_vec_add @
    store_vec_basic @
    store_add @
    store_basic @
    jmp_basic @
    br_zero @
    br_icmp @
    br_fcmp @
    call_basic @
    hlt @
    ret
end
