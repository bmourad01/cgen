open Core

module R = X86_amd64_common.Reg
module Rv = X86_amd64_common.Regvar

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

  let move_rr_x_y env =
    let*! x, xt = S.regvar env "x" in
    let*! y, yt = S.regvar env "y" in
    let*! () = guard @@ Type.equal_basic xt yt in
    if Rv.equal x y then !!![]
    else
      let dst = Oreg (x, xt) in
      let src = Oreg (y, yt) in
      match xt, yt with
      | (#Type.imm as xi), (#Type.imm as yi)
        when Type.equal_imm xi yi -> !!![MOV (dst, src)]
      | `f32, `f32 -> !!![MOVSS (dst, src)]
      | `f64, `f64 -> !!![MOVSD (dst, src)]
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
    !!![LEA (Oreg (x, xt), Omem addr)]

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
      !!![LEA (Oreg (x, xt), Omem (Abi (y, z)))]
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
    !!![LEA (Oreg (x, xt), Omem (Abis (y, z, s)))]

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
      !!![LEA (Oreg (x, xt), Omem (Abd (y, Dimm z)))]
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
      !!![LEA (Oreg (x, xt), Omem (Abd (y, Dimm z)))]
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


  let jcc_r_zero_x env =
    let*! x, xt = S.regvar env "x" in
    let*! yes = S.label env "yes" in
    let*! no = S.label env "no" in !!![
      TEST_ (Oreg (x, xt), Oreg (x, xt));
      Jcc (Ce, yes);
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
        Jcc (Cle, yes);
        JMP (Jlbl no);
      ]

  let setcc_r_zero_x_y ?(neg = false) env =
    let*! x, xt = S.regvar env "x" in
    let*! y, yt = S.regvar env "y" in
    let xt = match xt with
      | `i64 -> `i32
      | _ -> xt in
    let cc = if neg then Cne else Ce in
    let rax = Rv.reg `rax in
    match xt with
    | `i8 -> !!![
        TEST_ (Oreg (y, yt), Oreg (y, yt));
        SETcc (cc, Oreg (x, xt));
      ]
    | _ -> !!![
        TEST_ (Oreg (y, yt), Oreg (y, yt));
        SETcc (cc, Oreg (rax, `i8));
        MOVZX (Oreg (x, xt), Oreg (rax, `i8));
      ]

  let setcc_ri_x_y_z cc env =
    let*! x, xt = S.regvar env "x" in
    let*! y, yt = S.regvar env "y" in
    let*! z, zt = S.imm env "z" in
    let z = Bv.to_int64 z in
    let rax = Rv.reg `rax in
    let xt = match xt with
      | `i64 -> `i32
      | _ -> xt in
    match xt with
    | `i8 -> !!![
        CMP (Oreg (y, yt), Oimm (z, zt));
        SETcc (cc, Oreg (x, xt));
      ]
    | _ when fits_int32 z -> !!![
        CMP (Oreg (y, yt), Oimm (z, zt));
        SETcc (cc, Oreg (rax, `i8));
        MOVZX (Oreg (x, xt), Oreg (x, `i8));
      ]
    | _ ->
      let*! () = guard @@ Type.equal_basic yt `i64 in
      let+ z' = C.Var.fresh >>| Rv.var in
      Some [
        MOV (Oreg (z', `i64), Oimm (z, zt));
        CMP (Oreg (y, yt), Oreg (z', `i64));
        SETcc (cc, Oreg (rax, `i8));
        MOVZX (Oreg (x, xt), Oreg (rax, `i8));
      ]

  let load_rri_add_x_y_z env =
    let*! x, xt = S.regvar env "x" in
    let*! y, _ = S.regvar env "y" in
    let*! z, _ = S.imm env "z" in
    let z = Bv.to_int64 z in
    let*! () = guard @@ fits_int32 z in
    let z = Int64.to_int32_trunc z in !!![
      MOV (Oreg (x, xt), Omem (Abd (y, Dimm z)));
    ]

  let load_rr_x_y env =
    let*! x, xt = S.regvar env "x" in
    let*! y, _ = S.regvar env "y" in !!![
      MOV (Oreg (x, xt), Omem (Ab y));
    ]

  let store_rr_x_y env =
    let*! x, xt = S.regvar env "x" in
    let*! y, _ = S.regvar env "y" in !!![
      MOV (Omem (Ab y), Oreg (x, xt));
    ]

  let store_ri_x_y env =
    let*! x, xt = S.imm env "x" in
    let*! y, _ = S.regvar env "y" in !!![
      MOV (Omem (Ab y), Oimm (Bv.to_int64 x, xt));
    ]

  let store_rri_add_x_y_z env =
    let*! x, xt = S.regvar env "x" in
    let*! y, _ = S.regvar env "y" in
    let*! z, _ = S.imm env "z" in
    let z = Bv.to_int64 z in
    let*! () = guard @@ fits_int32 z in
    let z = Int64.to_int32_trunc z in
    !!![
      MOV (Omem (Abd (y, Dimm z)), Oreg (x, xt));
    ]

  let store_iri_add_x_y_z env =
    let*! x, xt = S.imm env "x" in
    let*! y, _ = S.regvar env "y" in
    let*! z, _ = S.imm env "z" in
    let z = Bv.to_int64 z in
    let*! () = guard @@ fits_int32 z in
    let z = Int64.to_int32_trunc z in
    let x = Bv.to_int64 x in
    !!![
      MOV (Omem (Abd (y, Dimm z)), Oimm (x, xt));
    ]

  let store_rsym_x_y env =
    let*! s, o = S.sym env "x" in
    let*! y, yt = S.regvar env "y" in
    let addr = Abd (Rv.reg `rip, Dsym (s, o)) in
    let* x = C.Var.fresh >>| Rv.var in !!![
      LEA (Oreg (x, `i64), Omem addr);
      MOV (Omem (Ab y), Oreg (x, yt))
    ]

  let store_symr_x_y env =
    let*! x, xt = S.regvar env "x" in
    let*! s, o = S.sym env "y" in
    let addr = Abd (Rv.reg `rip, Dsym (s, o)) in !!![
      MOV (Omem addr, Oreg (x, xt));
    ]

  let imul_rr_x_y_z env =
    let*! x, xt = S.regvar env "x" in
    let*! y, yt = S.regvar env "y" in
    let*! z, zt = S.regvar env "z" in !!![
      MOV (Oreg (x, xt), Oreg (y, yt));
      IMUL2 (Oreg (x, xt), Oreg (z, zt));
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

  let sext_rr_x_y env =
    let*! x, xt = S.regvar env "x" in
    let*! y, yt = S.regvar env "y" in
    if Type.equal_basic xt yt then !!![]
    else !!![MOVSX (Oreg (x, xt), Oreg (y, yt))]

  let zext_rr_x_y env =
    let*! x, xt = S.regvar env "x" in
    let*! y, yt = S.regvar env "y" in
    if Type.equal_basic xt yt then !!![]
    else match xt, yt with
      | `i64, `i32 ->
        (* Implicit zero-extension. *)
        !!![MOV (Oreg (x, `i32), Oreg (y, `i32))]
      | _ ->
        !!![MOVZX (Oreg (x, xt), Oreg (y, yt))]

  let call_sym_x env =
    let*! s, o = S.sym env "x" in
    !!![CALL (Osym (s, o))]

  let ret_ _ = !!![RET]
  let nop _ = !!![]

  (* The rules themselves. *)

  open P.Op

  let rules = [
    move x x => nop;

    move x (add `i32 y z) =>* [
      add_rr_x_y_z;
      add_ri_x_y_z;
    ];

    move x (add `i64 y (mul `i64 z (i64 1L))) => add_mul_rr_scale_x_y_z 1;
    move x (add `i64 y (mul `i64 z (i64 2L))) => add_mul_rr_scale_x_y_z 2;
    move x (add `i64 y (mul `i64 z (i64 4L))) => add_mul_rr_scale_x_y_z 4;
    move x (add `i64 y (mul `i64 z (i64 8L))) => add_mul_rr_scale_x_y_z 8;

    move x (add `i64 (mul `i64 z (i64 1L)) y) => add_mul_rr_scale_x_y_z 1;
    move x (add `i64 (mul `i64 z (i64 2L)) y) => add_mul_rr_scale_x_y_z 2;
    move x (add `i64 (mul `i64 z (i64 4L)) y) => add_mul_rr_scale_x_y_z 4;
    move x (add `i64 (mul `i64 z (i64 8L)) y) => add_mul_rr_scale_x_y_z 8;

    move x (add `i64 y (lsl_ `i64 z (i64 0L))) => add_mul_rr_scale_x_y_z 1;
    move x (add `i64 y (lsl_ `i64 z (i64 1L))) => add_mul_rr_scale_x_y_z 2;
    move x (add `i64 y (lsl_ `i64 z (i64 2L))) => add_mul_rr_scale_x_y_z 4;
    move x (add `i64 y (lsl_ `i64 z (i64 3L))) => add_mul_rr_scale_x_y_z 8;

    move x (add `i64 (lsl_ `i64 z (i64 0L)) y) => add_mul_rr_scale_x_y_z 1;
    move x (add `i64 (lsl_ `i64 z (i64 1L)) y) => add_mul_rr_scale_x_y_z 2;
    move x (add `i64 (lsl_ `i64 z (i64 2L)) y) => add_mul_rr_scale_x_y_z 4;
    move x (add `i64 (lsl_ `i64 z (i64 3L)) y) => add_mul_rr_scale_x_y_z 8;

    move x (add `i64 y z) =>* [
      add_rr_x_y_z;
      add_ri_x_y_z;
    ];

    move x (sub `i32 y z) =>* [
      sub_rr_x_y_z;
      sub_ri_x_y_z;
    ];

    move x (sub `i64 y z) =>* [
      sub_rr_x_y_z;
      sub_ri_x_y_z;
    ];

    move x (and_ `i64 y z) =>* [
      and_ri_x_y_z;
    ];

    move x (mul `i32 y z) =>* [
      imul_rr_x_y_z;
    ];

    move x (rem `i32 y z) =>* [
      idiv_rem_rr_x_y_z;
    ];

    move x (eq `i8 y (i8 0)) => setcc_r_zero_x_y;
    move x (eq `i16 y (i16 0)) => setcc_r_zero_x_y;
    move x (eq `i32 y (i32 0l)) => setcc_r_zero_x_y;
    move x (eq `i64 y (i64 0L)) => setcc_r_zero_x_y;

    move x (eq `i8 y z) =>* [
      setcc_ri_x_y_z Ce;
    ];

    move x (eq `i16 y z) =>* [
      setcc_ri_x_y_z Ce;
    ];

    move x (eq `i32 y z) =>* [
      setcc_ri_x_y_z Ce;
    ];

    move x (eq `i64 y z) =>* [
      setcc_ri_x_y_z Ce;
    ];

    move x (load `i32 (add `i64 y z)) =>* [
      load_rri_add_x_y_z;
    ];

    move x (load `i64 (add `i64 y z)) =>* [
      load_rri_add_x_y_z;
    ];

    move x (load `i32 y) =>* [
      load_rr_x_y;
    ];

    move x (load `i64 y) =>* [
      load_rr_x_y;
    ];

    move x (sext `i16 y) =>* [
      sext_rr_x_y;
    ];

    move x (sext `i32 y) =>* [
      sext_rr_x_y;
    ];

    move x (sext `i64 y) =>* [
      sext_rr_x_y;
    ];

    move x (zext `i16 y) =>* [
      zext_rr_x_y;
    ];

    move x (zext `i32 y) =>* [
      zext_rr_x_y;
    ];

    move x (zext `i64 y) =>* [
      zext_rr_x_y;
    ];

    move x y =>* [
      move_rr_x_y;
      move_ri_x_y;
      move_rb_x_y;
      move_rsym_x_y;
      move_rf32_x_y;
      move_rf64_x_y;
    ];

    store `i32 x y =>* [
      store_rr_x_y;
      store_ri_x_y;
      store_rsym_x_y;
      store_symr_x_y;
    ];

    store `i32 x (add `i64 y z) =>* [
      store_rri_add_x_y_z;
      store_iri_add_x_y_z;
    ];

    store `i64 x (add `i64 y z) =>* [
      store_rri_add_x_y_z;
      store_iri_add_x_y_z;
    ];

    store `i64 x y =>* [
      store_rr_x_y;
      store_ri_x_y;
      store_rsym_x_y;
      store_symr_x_y;
    ];

    jmp x =>* [
      jmp_lbl_x;
    ];

    br (eq `i32 x (i32 0l)) yes no => jcc_r_zero_x;
    br (eq `i64 x (i64 0L)) yes no => jcc_r_zero_x;

    br (eq `i32 x y) yes no =>* [
      jcc_ri_x_y Ce;
    ];

    br (eq `i64 x y) yes no =>* [
      jcc_ri_x_y Ce;
    ];

    br (le `i32 x y) yes no =>* [
      jcc_ri_x_y Cle;
    ];

    br (le `i64 x y) yes no =>* [
      jcc_ri_x_y Cle;
    ];

    ret => ret_;

    call x =>* [
      call_sym_x;
    ];
  ]
end
