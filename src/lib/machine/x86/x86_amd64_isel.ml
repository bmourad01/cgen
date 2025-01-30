open Core

module R = X86_amd64_common.Reg
module Rv = X86_amd64_common.Regvar
module I = X86_amd64_common.Insn

let (>*) x f = List.bind x ~f

let bty ty = (ty :> Type.basic)
let mty ty = (ty :> X86_amd64_common.Insn.memty)

external float_to_bits : float -> int64 = "cgen_bits_of_float"
external float_of_bits : int64 -> float = "cgen_float_of_bits"

let ftosi_ty = function
  | `i8 | `i16 | `i32 -> `i32
  | ty -> ty

let ftoui_ty = function
  | `i8 | `i16 -> `i32
  | `i32 -> `i64
  | ty -> ty

let xor_gpr_self x ty =
  (* Shorter instruction encoding when we use the 32-bit register,
     which is implicitly zero-extended to 64 bits. *)
  let ty = match ty with
    | `i64 -> `i32
    | _ -> ty in
  let x = I.Oreg (x, ty) in
  I.XOR (x, x)

let cwd_cdq_cqo (ty : Type.basic) = match ty with
  | `i16 -> I.CWD
  | `i32 -> I.CDQ
  | `i64 -> I.CQO
  | `i8 | #Type.fp -> assert false

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

(* pre: `tbl` is non-empty

   TODO:

   - Is int64 the right thing? Negative numbers could burn us.
   - What do we do about huge tables?
   - What is a good threshold for the lower-bound on the table?
*)
let adjust_table d tbl =
  let tbl = List.map tbl ~f:(fun (v, l) -> Bv.to_int64 v, l) in
  (* Assume that it's sorted. *)
  let lowest = fst @@ List.hd_exn tbl in
  let highest = fst @@ List.last_exn tbl in
  (* Pad the table with missing elements. *)
  let acc = Vec.create () in
  let _ = List.fold tbl ~init:lowest ~f:(fun p (v, l) ->
      let diff = Int64.(v - p) in
      for i = 0 to Int64.to_int_trunc diff - 1 do
        ignore i;
        Vec.push acc d;
      done;
      Vec.push acc l;
      Int64.succ v) in
  Vec.to_list acc, lowest, highest

module Make(C : Context_intf.S) : sig
  val rules : (Rv.t, I.t) Isel_rewrite.Rule(C).t list
end = struct
  open C.Syntax
  open Isel_rewrite.Rule(C)
  open I

  module P = Isel_rewrite.Pattern
  module S = Isel_rewrite.Subst

  let w = P.var "w"
  let x = P.var "x"
  let y = P.var "y"
  let z = P.var "z"
  let yes = P.var "yes"
  let no = P.var "no"

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
    else match xt with
      | #Type.imm -> !!![
          MOV (Oreg (x, xt), Oreg (y, yt));
          ADD (Oreg (x, xt), Oreg (z, zt));
        ]
      | `f64 -> !!![
          MOVSD (Oreg (x, xt), Oreg (y, yt));
          ADDSD (Oreg (x, xt), Oreg (z, zt));
        ]
      | `f32 -> !!![
          MOVSS (Oreg (x, xt), Oreg (y, yt));
          ADDSS (Oreg (x, xt), Oreg (z, zt));
        ]

  let add_mul_rr_scale_x_y_z s env =
    let*! x, xt = S.regvar env "x" in
    let*! y, _ = S.regvar env "y" in
    let*! z, _ = S.regvar env "z" in
    let*! () = guard @@ can_lea_ty xt in
    !!![LEA (Oreg (x, xt), Omem (Abis (y, z, s), `i64))]

  let add_mul_rr_scale_imm_x_y_z_w s env =
    let*! x, xt = S.regvar env "x" in
    let*! y, _ = S.regvar env "y" in
    let*! z, _ = S.regvar env "z" in
    let*! w, _ = S.imm env "w" in
    let w = Bv.to_int64 w in
    let*! () = guard @@ can_lea_ty xt in
    let*! () = guard @@ fits_int32_pos w in
    let w = Int64.to_int32_trunc w in
    !!![LEA (Oreg (x, xt), Omem (Abisd (y, z, s, Dimm w), `i64))]

  let add_mul_rr_scale_neg_imm_x_y_z_w s env =
    let*! x, xt = S.regvar env "x" in
    let*! y, _ = S.regvar env "y" in
    let*! z, _ = S.regvar env "z" in
    let*! w, _ = S.imm env "w" in
    let w = Bv.to_int64 w in
    let nw = Int64.neg w in
    let*! () = guard @@ can_lea_ty xt in
    let*! () = guard @@ fits_int32_neg nw in
    let w = Int64.to_int32_trunc nw in
    !!![LEA (Oreg (x, xt), Omem (Abisd (y, z, s, Dimm w), `i64))]

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

  let add_rf32_x_y_z env =
    let*! x, xt = S.regvar env "x" in
    let*! y, yt = S.regvar env "y" in
    let*! () = guard @@ Type.equal_basic xt yt in
    let*! z = S.single env "z" in !!![
      MOVSS (Oreg (x, xt), Oreg (y, yt));
      ADDSS (Oreg (x, xt), Ofp32 z);
    ]

  let add_rf64_x_y_z env =
    let*! x, xt = S.regvar env "x" in
    let*! y, yt = S.regvar env "y" in
    let*! () = guard @@ Type.equal_basic xt yt in
    let*! z = S.double env "z" in !!![
      MOVSD (Oreg (x, xt), Oreg (y, yt));
      ADDSD (Oreg (x, xt), Ofp64 z);
    ]

  let sub_rr_x_y_z env =
    let*! x, xt = S.regvar env "x" in
    let*! y, yt = S.regvar env "y" in
    let*! z, zt = S.regvar env "z" in
    let*! () = guard @@ Type.equal_basic xt yt in
    let*! () = guard @@ Type.equal_basic xt zt in
    match xt with
    | #Type.imm -> !!![
        MOV (Oreg (x, xt), Oreg (y, yt));
        SUB (Oreg (x, xt), Oreg (z, zt));
      ]
    | `f64 -> !!![
        MOVSD (Oreg (x, xt), Oreg (y, yt));
        SUBSD (Oreg (x, xt), Oreg (z, zt));
      ]
    | `f32 -> !!![
        MOVSS (Oreg (x, xt), Oreg (y, yt));
        SUBSS (Oreg (x, xt), Oreg (z, zt));
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

  let sub_rf32_x_y_z env =
    let*! x, xt = S.regvar env "x" in
    let*! y, yt = S.regvar env "y" in
    let*! () = guard @@ Type.equal_basic xt yt in
    let*! z = S.single env "z" in !!![
      MOVSS (Oreg (x, xt), Oreg (y, yt));
      SUBSS (Oreg (x, xt), Ofp32 z);
    ]

  let sub_rf64_x_y_z env =
    let*! x, xt = S.regvar env "x" in
    let*! y, yt = S.regvar env "y" in
    let*! () = guard @@ Type.equal_basic xt yt in
    let*! z = S.double env "z" in !!![
      MOVSD (Oreg (x, xt), Oreg (y, yt));
      SUBSD (Oreg (x, xt), Ofp64 z);
    ]

  let and_rr_x_y_z env =
    let*! x, xt = S.regvar env "x" in
    let*! y, yt = S.regvar env "y" in
    let*! z, zt = S.regvar env "z" in !!![
      MOV (Oreg (x, xt) , Oreg (y, yt));
      AND (Oreg (x, xt), Oreg (z, zt));
    ]

  let and_ri_x_y_z env =
    let*! x, xt = S.regvar env "x" in
    let*! y, yt = S.regvar env "y" in
    let*! z, zt = S.imm env "z" in !!![
      MOV (Oreg (x, xt) , Oreg (y, yt));
      AND (Oreg (x, xt), Oimm (Bv.to_int64 z, zt));
    ]

  let or_rr_x_y_z env =
    let*! x, xt = S.regvar env "x" in
    let*! y, yt = S.regvar env "y" in
    let*! z, zt = S.regvar env "z" in !!![
      MOV (Oreg (x, xt) , Oreg (y, yt));
      OR (Oreg (x, xt), Oreg (z, zt));
    ]

  let or_ri_x_y_z env =
    let*! x, xt = S.regvar env "x" in
    let*! y, yt = S.regvar env "y" in
    let*! z, zt = S.imm env "z" in !!![
      MOV (Oreg (x, xt) , Oreg (y, yt));
      OR (Oreg (x, xt), Oimm (Bv.to_int64 z, zt));
    ]

  let xor_ri_x_y_z env =
    let*! x, xt = S.regvar env "x" in
    let*! y, yt = S.regvar env "y" in
    let*! z, zt = S.imm env "z" in !!![
      MOV (Oreg (x, xt) , Oreg (y, yt));
      XOR (Oreg (x, xt), Oimm (Bv.to_int64 z, zt));
    ]

  let xor_rr_x_y_z env =
    let*! x, xt = S.regvar env "x" in
    let*! y, yt = S.regvar env "y" in
    let*! z, zt = S.regvar env "z" in !!![
      MOV (Oreg (x, xt) , Oreg (y, yt));
      XOR (Oreg (x, xt), Oreg (z, zt));
    ]

  let jmp_lbl_x env =
    let*! x = S.label env "x" in
    !!![JMP (Jlbl x)]

  let jmp_sym_x env =
    let*! s, o = S.sym env "x" in
    !!![JMP (Jind (Osym (s, o)))]

  let jcc_r_zero_x ?(neg = false) env =
    let*! x, xt = S.regvar env "x" in
    let*! yes = S.label env "yes" in
    let*! no = S.label env "no" in
    let cc = if neg then Cne else Ce in !!![
      TEST_ (Oreg (x, xt), Oreg (x, xt));
      Jcc (cc, yes);
      JMP (Jlbl no);
    ]

  let jcc_r_less_than_zero_x ?(neg = false) env =
    let*! x, xt = S.regvar env "x" in
    let*! yes = S.label env "yes" in
    let*! no = S.label env "no" in
    let cc = if neg then Cns else Cs in !!![
      TEST_ (Oreg (x, xt), Oreg (x, xt));
      Jcc (cc, yes);
      JMP (Jlbl no);
    ]

  let jcc_rr_test_x_y ?(neg = false) env =
    let*! x, xt = S.regvar env "x" in
    let*! y, yt = S.regvar env "y" in
    let*! yes = S.label env "yes" in
    let*! no = S.label env "no" in
    let cc = if neg then Ce else Cne in !!![
      TEST_ (Oreg (x, xt), Oreg (y, yt));
      Jcc (cc, yes);
      JMP (Jlbl no);
    ]

  let jcc_ri_test_x_y ?(neg = false) env =
    let*! x, xt = S.regvar env "x" in
    let*! y, yt = S.imm env "y" in
    let*! yes = S.label env "yes" in
    let*! no = S.label env "no" in
    let cc = if neg then Ce else Cne in !!![
      TEST_ (Oreg (x, xt), Oimm (Bv.to_int64 y, yt));
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
  let setcc_r_less_than_zero_x_y ?(neg = false) env =
    let*! x, _ = S.regvar env "x" in
    let*! y, yt = S.regvar env "y" in
    let cc = if neg then Cns else Cs in !!![
      TEST_ (Oreg (y, yt), Oreg (y, yt));
      SETcc (cc, Oreg (x, `i8));
    ]

  (* Default to 8-bit *)
  let setcc_rr_test_x_y_z ?(neg = false) env =
    let*! x, _ = S.regvar env "x" in
    let*! y, yt = S.regvar env "y" in
    let*! z, zt = S.regvar env "z" in
    let cc = if neg then Ce else Cne in !!![
      TEST_ (Oreg (y, yt), Oreg (z, zt));
      SETcc (cc, Oreg (x, `i8));
    ]

  (* Default to 8-bit *)
  let setcc_ri_test_x_y_z ?(neg = false) env =
    let*! x, _ = S.regvar env "x" in
    let*! y, yt = S.regvar env "y" in
    let*! z, zt = S.imm env "z" in
    let cc = if neg then Ce else Cne in !!![
      TEST_ (Oreg (y, yt), Oimm (Bv.to_int64 z, zt));
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

  (* 8-bit cmov is not supported, but we can just use
     the 32-bit variant and pretend that nothing happened.

     If the input program is well-typed then this should
     be kosher.
  *)
  let sel_i8_ty = function
    | `i8 -> `i32
    | t -> t

  let sel_rrrr_x_y_z cc env =
    let*! x, xt = S.regvar env "x" in
    let*! y, yt = S.regvar env "y" in
    let*! z, zt = S.regvar env "z" in
    let*! yes, yes_t = S.regvar env "yes" in
    let*! no, no_t = S.regvar env "no" in
    let*! () = guard @@ Type.equal_basic xt yes_t in
    let*! () = guard @@ Type.equal_basic xt no_t in
    let xt = sel_i8_ty xt in !!![
      MOV (Oreg (x, xt), Oreg (no, xt));
      CMP (Oreg (y, yt), Oreg (z, zt));
      CMOVcc (cc, Oreg (x, xt), Oreg (yes, xt));
    ]

  let sel_rirr_x_y_z cc env =
    let*! x, xt = S.regvar env "x" in
    let*! y, yt = S.regvar env "y" in
    let*! z, zt = S.imm env "z" in
    let*! yes, yes_t = S.regvar env "yes" in
    let*! no, no_t = S.regvar env "no" in
    let*! () = guard @@ Type.equal_basic xt yes_t in
    let*! () = guard @@ Type.equal_basic xt no_t in
    let xt = sel_i8_ty xt in
    let z = Bv.to_int64 z in
    if fits_int32 z then !!![
        MOV (Oreg (x, xt), Oreg (no, xt));
        CMP (Oreg (y, yt), Oimm (z, zt));
        CMOVcc (cc, Oreg (x, xt), Oreg (yes, xt));
      ]
    else
      let* tmp = C.Var.fresh >>| Rv.var in !!![
        MOV (Oreg (tmp, bty zt), Oimm (z, zt));
        MOV (Oreg (x, xt), Oreg (no, xt));
        CMP (Oreg (y, yt), Oreg (tmp, bty zt));
        CMOVcc (cc, Oreg (x, xt), Oreg (yes, xt));
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

  let imul8_rr_x_y_z env =
    let*! x, xt = S.regvar env "x" in
    let*! y, yt = S.regvar env "y" in
    let*! z, zt = S.regvar env "z" in
    let rax = Rv.reg `rax in !!![
      MOVZX (Oreg (rax, `i16), Oreg (y, yt));
      IMUL1 (Oreg (z, zt));
      MOV (Oreg (x, xt), Oreg (rax, `i8));
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

  let imul8_rr_high_x_y_z env =
    let*! x, xt = S.regvar env "x" in
    let*! y, yt = S.regvar env "y" in
    let*! z, zt = S.regvar env "z" in
    let rax = Rv.reg `rax in !!![
      MOVZX (Oreg (rax, `i16), Oreg (y, yt));
      IMUL1 (Oreg (z, zt));
      MOV (Oreg (x, xt), Oah);
    ]

  let imul8_ri_high_x_y_z env =
    let*! x, xt = S.regvar env "x" in
    let*! y, yt = S.regvar env "y" in
    let*! z, zt = S.imm env "z" in
    let z = Bv.to_int64 z in
    let rax = Rv.reg `rax in !!![
      MOVZX (Oreg (rax, `i16), Oimm (z, zt));
      IMUL1 (Oreg (y, yt));
      MOV (Oreg (x, xt), Oah);
    ]

  let mul8_rr_high_x_y_z env =
    let*! x, xt = S.regvar env "x" in
    let*! y, yt = S.regvar env "y" in
    let*! z, zt = S.regvar env "z" in
    let rax = Rv.reg `rax in !!![
      MOVZX (Oreg (rax, `i16), Oreg (y, yt));
      MUL (Oreg (z, zt));
      MOV (Oreg (x, xt), Oah);
    ]

  let mul8_ri_high_x_y_z env =
    let*! x, xt = S.regvar env "x" in
    let*! y, yt = S.regvar env "y" in
    let*! z, zt = S.imm env "z" in
    let z = Bv.to_int64 z in
    let rax = Rv.reg `rax in !!![
      MOVZX (Oreg (rax, `i16), Oimm (z, zt));
      MUL (Oreg (y, yt));
      MOV (Oreg (x, xt), Oah);
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

  let fmul_rr_x_y_z env =
    let*! x, xt = S.regvar env "x" in
    let*! y, yt = S.regvar env "y" in
    let*! z, zt = S.regvar env "z" in
    match xt with
    | `f64 -> !!![
        MOVSD (Oreg (x, xt), Oreg (y, yt));
        MULSD (Oreg (x, xt), Oreg (z, zt));
      ]
    | `f32 -> !!![
        MOVSS (Oreg (x, xt), Oreg (y, yt));
        MULSS (Oreg (x, xt), Oreg (z, zt));
      ]
    | _ -> !!None

  let fmul_rf32_x_y_z env =
    let*! x, xt = S.regvar env "x" in
    let*! y, yt = S.regvar env "y" in
    let*! z = S.single env "z" in
    let*! () = guard (Type.equal_basic xt `f32) in !!![
      MOVSS (Oreg (x, xt), Oreg (y, yt));
      MULSS (Oreg (x, xt), Ofp32 z);
    ]

  let fmul_rf64_x_y_z env =
    let*! x, xt = S.regvar env "x" in
    let*! y, yt = S.regvar env "y" in
    let*! z = S.double env "z" in
    let*! () = guard (Type.equal_basic xt `f64) in !!![
      MOVSD (Oreg (x, xt), Oreg (y, yt));
      MULSD (Oreg (x, xt), Ofp64 z);
    ]

  let idiv_rem_rr_x_y_z env =
    let*! x, xt = S.regvar env "x" in
    let*! y, yt = S.regvar env "y" in
    let*! z, zt = S.regvar env "z" in
    let rax = Rv.reg `rax in
    let rdx = Rv.reg `rdx in !!![
      MOV (Oreg (rax, yt), Oreg (y, yt));
      cwd_cdq_cqo yt;
      IDIV (Oreg (z, zt));
      MOV (Oreg (x, xt), Oreg (rdx, xt));
    ]

  let idiv_rr_x_y_z env =
    let*! x, xt = S.regvar env "x" in
    let*! y, yt = S.regvar env "y" in
    let*! z, zt = S.regvar env "z" in
    let rax = Rv.reg `rax in !!![
      MOV (Oreg (rax, yt), Oreg (y, yt));
      cwd_cdq_cqo yt;
      IDIV (Oreg (z, zt));
      MOV (Oreg (x, xt), Oreg (rax, xt));
    ]

  let idiv8_rr_x_y_z env =
    let*! x, xt = S.regvar env "x" in
    let*! y, yt = S.regvar env "y" in
    let*! z, zt = S.regvar env "z" in
    let rax = Rv.reg `rax in !!![
      MOVZX (Oreg (rax, `i16), Oreg (y, yt));
      CWD;
      IDIV (Oreg (z, zt));
      MOV (Oreg (x, xt), Oreg (rax, `i8));
    ]

  let idiv8_rem_rr_x_y_z env =
    let*! x, xt = S.regvar env "x" in
    let*! y, yt = S.regvar env "y" in
    let*! z, zt = S.regvar env "z" in
    let rax = Rv.reg `rax in !!![
      MOVZX (Oreg (rax, `i16), Oreg (y, yt));
      CWD;
      IDIV (Oreg (z, zt));
      MOV (Oreg (x, xt), Oah);
    ]

  let div8_rem_rr_x_y_z env =
    let*! x, xt = S.regvar env "x" in
    let*! y, yt = S.regvar env "y" in
    let*! z, zt = S.regvar env "z" in
    let rax = Rv.reg `rax in
    let rdx = Rv.reg `rdx in !!![
      MOVZX (Oreg (rax, `i16), Oreg (y, yt));
      XOR (Oreg (rdx, `i32), Oreg (rdx, `i32));
      DIV (Oreg (z, zt));
      MOV (Oreg (x, xt), Oah);
    ]

  let div_rem_rr_x_y_z env =
    let*! x, xt = S.regvar env "x" in
    let*! y, yt = S.regvar env "y" in
    let*! z, zt = S.regvar env "z" in
    let rax = Rv.reg `rax in
    let rdx = Rv.reg `rdx in !!![
      MOV (Oreg (rax, yt), Oreg (y, yt));
      XOR (Oreg (rdx, `i32), Oreg (rdx, `i32));
      DIV (Oreg (z, zt));
      MOV (Oreg (x, xt), Oreg (rdx, xt));
    ]

  let fdiv_rr_x_y_z env =
    let*! x, xt = S.regvar env "x" in
    let*! y, yt = S.regvar env "y" in
    let*! z, zt = S.regvar env "z" in
    match xt with
    | `f64 -> !!![
        MOVSD (Oreg (x, xt), Oreg (y, yt));
        DIVSD (Oreg (x, xt), Oreg (z, zt));
      ]
    | `f32 -> !!![
        MOVSS (Oreg (x, xt), Oreg (y, yt));
        DIVSS (Oreg (x, xt), Oreg (z, zt));
      ]
    | _ -> !!None

  let fdiv_rf32_x_y_z env =
    let*! x, xt = S.regvar env "x" in
    let*! y, yt = S.regvar env "y" in
    let*! z = S.single env "z" in
    let*! () = guard (Type.equal_basic xt `f32) in !!![
      MOVSS (Oreg (x, xt), Oreg (y, yt));
      DIVSS (Oreg (x, xt), Ofp32 z);
    ]

  let fdiv_rf64_x_y_z env =
    let*! x, xt = S.regvar env "x" in
    let*! y, yt = S.regvar env "y" in
    let*! z = S.double env "z" in
    let*! () = guard (Type.equal_basic xt `f64) in !!![
      MOVSD (Oreg (x, xt), Oreg (y, yt));
      DIVSD (Oreg (x, xt), Ofp64 z);
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

  let rol_rr_x_y_z env =
    let*! x, xt = S.regvar env "x" in
    let*! y, yt = S.regvar env "y" in
    let*! z, _ = S.regvar env "z" in
    let rcx = Rv.reg `rcx in !!![
      MOV (Oreg (x, xt), Oreg (y, yt));
      MOV (Oreg (rcx, `i8), Oreg (z, `i8));
      ROL (Oreg (x, xt), Oreg (rcx, `i8));
    ]

  let rol_ri_x_y_z env =
    let*! x, xt = S.regvar env "x" in
    let*! y, yt = S.regvar env "y" in
    let*! z, _ = S.imm env "z" in
    let z = Bv.to_int64 z in !!![
      MOV (Oreg (x, xt), Oreg (y, yt));
      ROL (Oreg (x, xt), Oimm (Int64.(z land 0xFFL), `i8));
    ]

  let ror_rr_x_y_z env =
    let*! x, xt = S.regvar env "x" in
    let*! y, yt = S.regvar env "y" in
    let*! z, _ = S.regvar env "z" in
    let rcx = Rv.reg `rcx in !!![
      MOV (Oreg (x, xt), Oreg (y, yt));
      MOV (Oreg (rcx, `i8), Oreg (z, `i8));
      ROR (Oreg (x, xt), Oreg (rcx, `i8));
    ]

  let ror_ri_x_y_z env =
    let*! x, xt = S.regvar env "x" in
    let*! y, yt = S.regvar env "y" in
    let*! z, _ = S.imm env "z" in
    let z = Bv.to_int64 z in !!![
      MOV (Oreg (x, xt), Oreg (y, yt));
      ROR (Oreg (x, xt), Oimm (Int64.(z land 0xFFL), `i8));
    ]

  let neg_r_x_y env =
    let*! x, xt = S.regvar env "x" in
    let*! y, yt = S.regvar env "y" in !!![
      MOV (Oreg (x, xt), Oreg (y, yt));
      NEG (Oreg (x, xt));
    ]

  let neg_i_x_y env =
    let*! x, xt = S.regvar env "x" in
    let*! y, yt = S.imm env "y" in
    match Virtual.Eval.unop_int (`neg (bty yt)) y yt with
    | Some `int (i, _) ->
      !!![MOV (Oreg (x, xt), Oimm (Bv.to_int64 i, yt))]
    | _ ->
      (* shouldn't fail *)
      !!None

  (* NB: this is a bit of a kludge, which will require special handling
     after isel. *)
  let fneg_r_x_y env =
    let*! x, xt = S.regvar env "x" in
    let*! y, yt = S.regvar env "y" in
    match xt with
    | `f32 -> !!![
        MOVSS (Oreg (x, xt), Oreg (y, yt));
        XORPS (Oreg (x, xt), Ofp32 (Float32.of_bits 0x8000_0000l));
      ]
    | `f64 -> !!![
        MOVSD (Oreg (x, xt), Oreg (y, yt));
        XORPD (Oreg (x, xt), Ofp64 (float_of_bits 0x8000_0000_0000_0000L));
      ]
    | _ -> !!None

  let fneg_fp32_x_y env =
    let*! x, xt = S.regvar env "x" in
    let*! y = S.single env "y" in
    let*! () = guard (Type.equal_basic xt `f32) in !!![
      MOVSS (Oreg (x, xt), Ofp32 (Float32.neg y));
    ]

  let fneg_fp64_x_y env =
    let*! x, xt = S.regvar env "x" in
    let*! y = S.double env "y" in
    let*! () = guard (Type.equal_basic xt `f64) in !!![
      MOVSD (Oreg (x, xt), Ofp64 (Float.neg y));
    ]

  let not_r_x_y env =
    let*! x, xt = S.regvar env "x" in
    let*! y, yt = S.regvar env "y" in !!![
      MOV (Oreg (x, xt), Oreg (y, yt));
      NOT (Oreg (x, xt));
    ]

  let not_i_x_y env =
    let*! x, xt = S.regvar env "x" in
    let*! y, yt = S.imm env "y" in
    match Virtual.Eval.unop_int (`not_ yt) y yt with
    | Some `int (i, _) ->
      !!![MOV (Oreg (x, xt), Oimm (Bv.to_int64 i, yt))]
    | _ ->
      !!![
        MOV (Oreg (x, xt), Oimm (Bv.to_int64 y, yt));
        NOT (Oreg (x, xt));
      ]

  let clz_r_x_y env =
    let*! x, xt = S.regvar env "x" in
    let*! y, yt = S.regvar env "y" in !!![
      LZCNT (Oreg (x, xt), Oreg (y, yt));
    ]

  (* Idea:

     Zero-extend to 16 bits, shift left by 8, and with 255,
     and then do the LZCNT. The operand size will be the result
     in the case of the input being zero, as specified in the
     manual, although we reserve that the result can be undefined.
  *)
  let clz8_r_x_y env =
    let*! x, xt = S.regvar env "x" in
    let*! y, yt = S.regvar env "y" in
    let* tmp1 = C.Var.fresh >>| Rv.var in
    let* tmp2 = C.Var.fresh >>| Rv.var in !!![
      MOVZX (Oreg (tmp1, `i16), Oreg (y, yt));
      SHL (Oreg (tmp1, `i16), Oimm (8L, `i8));
      AND (Oreg (tmp1, `i16), Oimm (0xFFL, `i16));
      LZCNT (Oreg (tmp2, `i16), Oreg (tmp1, `i16));
      MOV (Oreg (x, xt), Oreg (tmp2, `i8));
    ]

  let ctz_r_x_y env =
    let*! x, xt = S.regvar env "x" in
    let*! y, yt = S.regvar env "y" in !!![
      TZCNT (Oreg (x, xt), Oreg (y, yt));
    ]

  (* Same idea as the clz case, but we fill the upper 8 bits. *)
  let ctz8_r_x_y env =
    let*! x, xt = S.regvar env "x" in
    let*! y, yt = S.regvar env "y" in
    let* tmp1 = C.Var.fresh >>| Rv.var in
    let* tmp2 = C.Var.fresh >>| Rv.var in !!![
      MOVZX (Oreg (tmp1, `i16), Oreg (y, yt));
      AND (Oreg (tmp1, `i16), Oimm (0xFF00L, `i16));
      TZCNT (Oreg (tmp2, `i16), Oreg (tmp1, `i16));
      MOV (Oreg (x, xt), Oreg (tmp2, `i8));
    ]

  let popcnt_r_x_y env =
    let*! x, xt = S.regvar env "x" in
    let*! y, yt = S.regvar env "y" in !!![
      POPCNT (Oreg (x, xt), Oreg (y, yt));
    ]

  (* Here we should be safe with just a zero-extend. *)
  let popcnt8_r_x_y env =
    let*! x, xt = S.regvar env "x" in
    let*! y, yt = S.regvar env "y" in
    let* tmp1 = C.Var.fresh >>| Rv.var in
    let* tmp2 = C.Var.fresh >>| Rv.var in !!![
      MOVZX (Oreg (tmp1, `i16), Oreg (y, yt));
      POPCNT (Oreg (tmp2, `i16), Oreg (tmp1, `i16));
      MOV (Oreg (x, xt), Oreg (tmp2, `i8));
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

  let fext_rr_x_y ty env =
    let*! x, xt = S.regvar env "x" in
    let*! y, yt = S.regvar env "y" in
    match ty, xt, yt with
    | `f32, `f32, `f32 ->
      !!![MOVSS (Oreg (x, xt), Oreg (y, yt))]
    | `f64, `f64, `f64 ->
      !!![MOVSD (Oreg (x, xt), Oreg (y, yt))]
    | `f64, `f64, `f32 -> !!![
        XORPD (Oreg (x, xt), Oreg (x, xt));
        CVTSS2SD (Oreg (x, xt), Oreg (y, yt))
      ]
    | _ -> !!None

  let fext_rf32_x_y ty env =
    let*! x, xt = S.regvar env "x" in
    let*! y = S.single env "y" in
    match ty, xt with
    | `f32, `f32 ->
      !!![MOVSS (Oreg (x, xt), Ofp32 y)]
    | `f64, `f64 ->
      let y' = Float32.to_float y in
      !!![MOVSD (Oreg (x, xt), Ofp64 y')]
    | _ -> !!None

  let fext_rf64_x_y ty env =
    let*! x, xt = S.regvar env "x" in
    let*! y = S.double env "y" in
    match ty, xt with
    | `f64, `f64 ->
      !!![MOVSD (Oreg (x, xt), Ofp64 y)]
    | _ -> !!None

  let fibits_rr_x_y ty env =
    let*! x, xt = S.regvar env "x" in
    let*! y, yt = S.regvar env "y" in
    match ty, xt, yt with
    | `f32, `f32, `i32 ->
      !!![MOVD (Oreg (x, xt), Oreg (y, yt))]
    | `f64, `f64, `i64 ->
      !!![MOVQ (Oreg (x, xt), Oreg (y, yt))]
    | _ -> !!None

  let fibits_ri_x_y ty env =
    let*! x, xt = S.regvar env "x" in
    let*! y, yt = S.imm env "y" in
    let*! () = guard (Type.equal_basic (ty :> Type.basic) xt) in
    match Virtual.Eval.unop_int (`fibits ty) y yt with
    | Some `float f ->
      !!![MOVSS (Oreg (x, xt), Ofp32 f)]
    | Some `double d ->
      !!![MOVSD (Oreg (x, xt), Ofp64 d)]
    | _ -> !!None

  let ftosi_rr_x_y tf ti env =
    let*! x, xt = S.regvar env "x" in
    let*! y, yt = S.regvar env "y" in
    let*! () = guard (Type.equal_basic (ti :> Type.basic) xt) in
    let*! () = guard (Type.equal_basic (tf :> Type.basic) yt) in
    let xt' = ftosi_ty xt in
    match tf with
    | `f32 ->
      !!![CVTSS2SI (Oreg (x, xt'), Oreg (y, yt))]
    | `f64 ->
      !!![CVTSD2SI (Oreg (x, xt'), Oreg (y, yt))]
    | _ -> !!None

  let ftosi_rf32_x_y ti env =
    let*! x, xt = S.regvar env "x" in
    let*! y = S.single env "y" in
    let*! () = guard (Type.equal_basic (ti :> Type.basic) xt) in
    match Virtual.Eval.unop_single (`ftosi (`f32, ti)) y with
    | Some `int (y', yt) ->
      !!![MOV (Oreg (x, xt), Oimm (Bv.to_int64 y', yt))]
    | _ -> !!None

  let ftosi_rf64_x_y ti env =
    let*! x, xt = S.regvar env "x" in
    let*! y = S.double env "y" in
    let*! () = guard (Type.equal_basic (ti :> Type.basic) xt) in
    match Virtual.Eval.unop_double (`ftosi (`f64, ti)) y with
    | Some `int (y', yt) ->
      !!![MOV (Oreg (x, xt), Oimm (Bv.to_int64 y', yt))]
    | _ -> !!None

  let ftoui_rr_x_y tf ti env =
    let*! x, xt = S.regvar env "x" in
    let*! y, yt = S.regvar env "y" in
    let*! () = guard (Type.equal_basic (ti :> Type.basic) xt) in
    let*! () = guard (Type.equal_basic (tf :> Type.basic) yt) in
    let xt' = ftoui_ty xt in
    match tf with
    | `f32 ->
      !!![CVTSS2SI (Oreg (x, xt'), Oreg (y, yt))]
    | `f64 ->
      !!![CVTSD2SI (Oreg (x, xt'), Oreg (y, yt))]
    | _ -> !!None

  let ftoui_rf32_x_y ti env =
    let*! x, xt = S.regvar env "x" in
    let*! y = S.single env "y" in
    let*! () = guard (Type.equal_basic (ti :> Type.basic) xt) in
    match Virtual.Eval.unop_single (`ftoui (`f32, ti)) y with
    | Some `int (y', yt) ->
      !!![MOV (Oreg (x, xt), Oimm (Bv.to_int64 y', yt))]
    | _ -> !!None

  let ftoui_rf64_x_y ti env =
    let*! x, xt = S.regvar env "x" in
    let*! y = S.double env "y" in
    let*! () = guard (Type.equal_basic (ti :> Type.basic) xt) in
    match Virtual.Eval.unop_double (`ftoui (`f64, ti)) y with
    | Some `int (y', yt) ->
      !!![MOV (Oreg (x, xt), Oimm (Bv.to_int64 y', yt))]
    | _ -> !!None

  let ftrunc_rr_x_y ty env =
    let*! x, xt = S.regvar env "x" in
    let*! y, yt = S.regvar env "y" in
    match ty, xt, yt with
    | `f64, `f64, `f64 ->
      !!![MOVSD (Oreg (x, xt), Oreg (y, yt))]
    | `f32, `f32, `f32 ->
      !!![MOVSS (Oreg (x, xt), Oreg (y, yt))]
    | `f32, `f32, `f64 -> !!![
        XORPS (Oreg (x, xt), Oreg (x, xt));
        CVTSD2SS (Oreg (x, xt), Oreg (y, yt))
      ]
    | _ -> !!None

  let ftrunc_rf32_x_y ty env =
    let*! x, xt = S.regvar env "x" in
    let*! y = S.single env "y" in
    match ty, xt with
    | `f32, `f32 ->
      !!![MOVSS (Oreg (x, xt), Ofp32 y)]
    | _ -> !!None

  let ftrunc_rf64_x_y ty env =
    let*! x, xt = S.regvar env "x" in
    let*! y = S.double env "y" in
    match ty, xt with
    | `f32, `f32 ->
      !!![MOVSS (Oreg (x, xt), Ofp64 y)]
    | `f64, `f64 ->
      !!![MOVSD (Oreg (x, xt), Ofp64 y)]
    | _ -> !!None

  let ifbits_rr_x_y ty env =
    let*! x, xt = S.regvar env "x" in
    let*! y, yt = S.regvar env "y" in
    let*! () = guard (Type.equal_basic (ty :> Type.basic) xt) in
    match ty, yt with
    | `i32, `f32 ->
      !!![MOVD (Oreg (x, xt), Oreg (y, yt))]
    | `i64, `f64 ->
      !!![MOVQ (Oreg (x, xt), Oreg (y, yt))]
    | _ -> !!None

  let ifbits_rf32_x_y ty env =
    let*! x, xt = S.regvar env "x" in
    let*! y = S.single env "y" in
    match ty, xt with
    | `i32, `i32 ->
      let y' = Int64.(of_int32 (Float32.bits y) land 0xFFFFFFFFL) in
      !!![MOV (Oreg (x, xt), Oimm (y', `i32))]
    | _ -> !!None

  let ifbits_rf64_x_y ty env =
    let*! x, xt = S.regvar env "x" in
    let*! y = S.double env "y" in
    match ty, xt with
    | `i64, `i64 ->
      !!![MOV (Oreg (x, xt), Oimm (float_to_bits y, `i64))]
    | _ -> !!None

  let itrunc_rr_x_y ty env =
    let*! x, xt = S.regvar env "x" in
    let*! y, _ = S.regvar env "y" in
    let*! () = guard (Type.equal_basic (ty :> Type.basic) xt) in
    (* Assume the width of the destination. *)
    !!![MOV (Oreg (x, xt), Oreg (y, xt))]

  let itrunc_ri_x_y ty env =
    let*! x, xt = S.regvar env "x" in
    let*! y, yt = S.imm env "y" in
    let*! () = guard (Type.equal_basic (ty :> Type.basic) xt) in
    match Virtual.Eval.unop_int (`itrunc ty) y yt with
    | Some `int (y', yt') ->
      !!![MOV (Oreg (x, xt), Oimm (Bv.to_int64 y', yt'))]
    | _ -> !!None

  let sitof_rr_x_y ti tf env =
    let*! x, xt = S.regvar env "x" in
    let*! y, yt = S.regvar env "y" in
    let*! () = guard (Type.equal_basic (tf :> Type.basic) xt) in
    let*! () = guard (Type.equal_basic (ti :> Type.basic) yt) in
    match ti, tf with
    | (`i8 | `i16), `f32 ->
      let* tmp = C.Var.fresh >>| Rv.var in !!![
        MOVZX (Oreg (tmp, `i32), Oreg (y, yt));
        XORPS (Oreg (x, xt), Oreg (x, xt));
        CVTSI2SS (Oreg (x, xt), Oreg (tmp, `i32));
      ]
    | `i32, `f32 ->
      let* tmp = C.Var.fresh >>| Rv.var in !!![
        MOV (Oreg (tmp, `i32), Oreg (y, yt));
        XORPS (Oreg (x, xt), Oreg (x, xt));
        CVTSI2SS (Oreg (x, xt), Oreg (tmp, `i64));
      ]
    | `i64, `f32 -> !!![
        XORPS (Oreg (x, xt), Oreg (x, xt));
        CVTSI2SS (Oreg (x, xt), Oreg (y, yt));
      ]
    | (`i8 | `i16), `f64 ->
      let* tmp = C.Var.fresh >>| Rv.var in !!![
        MOVZX (Oreg (tmp, `i32), Oreg (y, yt));
        XORPD (Oreg (x, xt), Oreg (x, xt));
        CVTSI2SD (Oreg (x, xt), Oreg (tmp, `i32));
      ]
    | `i32, `f64 ->
      let* tmp = C.Var.fresh >>| Rv.var in !!![
        MOV (Oreg (tmp, `i32), Oreg (y, yt));
        XORPD (Oreg (x, xt), Oreg (x, xt));
        CVTSI2SD (Oreg (x, xt), Oreg (tmp, `i64));
      ]
    | `i64, `f64 -> !!![
        XORPD (Oreg (x, xt), Oreg (x, xt));
        CVTSI2SD (Oreg (x, xt), Oreg (y, yt));
      ]

  let sitof_ri_x_y ti tf env =
    let*! x, xt = S.regvar env "x" in
    let*! y, yt = S.imm env "y" in
    let*! () = guard (Type.equal_basic (tf :> Type.basic) xt) in
    let*! () = guard (Type.equal_imm (ti :> Type.imm) yt) in
    match Virtual.Eval.unop_int (`sitof (ti, tf)) y yt with
    | Some `float f ->
      !!![MOVSS (Oreg (x, xt), Ofp32 f)]
    | Some `double d ->
      !!![MOVSD (Oreg (x, xt), Ofp64 d)]
    | _ -> !!None

  let call_sym_x env =
    let*! s, o = S.sym env "x" in
    !!![CALL (Osym (s, o))]

  let jmp_tbl_x_y env =
    let*! x, xt = S.regvar env "x" in
    let*! d, tbl = S.table env "y" in
    match xt, tbl with
    | _, [] ->
      (* Just jump to the default label. *)
      !!![JMP (Jlbl d)]
    | #Type.fp, _ ->
      (* Should be impossible. *)
      !!None
    | #Type.imm as xt, _ ->
      let tbl, lowest, highest = adjust_table d tbl in
      let highest' = Int64.(highest - lowest) in
      let diff = Int64.(highest - highest') in
      let* tl = C.Label.fresh in
      let* tbase = C.Var.fresh >>| Rv.var in
      let* tidx = C.Var.fresh >>| Rv.var in
      let rax = Rv.reg `rax in
      (!!!) @@ List.concat [
        (* Compare against the lowest value, if necessary. *)
        ( if Int64.(lowest = 1L) then [
              TEST_ (Oreg (x, xt), Oreg (x, xt));
              Jcc (Ce, d);
            ]
          else if Int64.(lowest > 0L) then [
            CMP (Oreg (x, xt), Oimm (lowest, xt));
            Jcc (Cb, d);
          ]
          else []
        );
        (* Zero-extend the index. *)
        [ match xt with
          | `i8 | `i16 ->
            MOVZX (Oreg (tidx, `i64), Oreg (x, xt))
          | `i32 | `i64 ->
            (* i32 has implicit zero-extension. *)
            MOV (Oreg (tidx, xt), Oreg (x, xt))
        ];
        (* Subtract the difference from the index if needed. *)
        ( if Int64.(diff = 1L)
          then [DEC (Oreg (tidx, `i64))]
          else if Int64.(diff > 0L)
          then [SUB (Oreg (tidx, `i64), Oimm (diff, `i64))]
          else []
        );
        [ (* Compare against highest value. *)
          CMP (Oreg (tidx, `i64), Oimm (highest', `i64));
          Jcc (Ca, d);
          (* Get the base of the table. *)
          LEA (Oreg (tbase, `i64), Omem (Abd (Reg `rip, Dlbl tl), `i64));
          (* Jump to the table entry. *)
          MOVSXD (Oreg (rax, `i64), Omem (Abis (tbase, tidx, 4), `i32));
          ADD (Oreg (rax, `i64), Oreg (tbase, `i64));
          JMP (Jind (Oreg (rax, `i64)));
          (* The table itself. *)
          JMPtbl (tl, tbl);
        ]
      ]

  open P.Op

  (* Re-used groups of callbacks. *)
  module Group = struct
    let add = [
      add_rr_x_y_z;
      add_ri_x_y_z;
      add_rf32_x_y_z;
      add_rf64_x_y_z;
    ]

    let sub = [
      sub_rr_x_y_z;
      sub_ri_x_y_z;
      sub_rf32_x_y_z;
      sub_rf64_x_y_z;
    ]

    let and_ = [
      and_rr_x_y_z;
      and_ri_x_y_z;
    ]

    let or_ = [
      or_rr_x_y_z;
      or_ri_x_y_z;
    ]

    let xor = [
      xor_rr_x_y_z;
      xor_ri_x_y_z;
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

    let rol = [
      rol_rr_x_y_z;
      rol_ri_x_y_z;
    ]

    let ror = [
      ror_rr_x_y_z;
      ror_ri_x_y_z;
    ]

    let mul = [
      imul_rr_x_y_z;
      imul_ri_x_y_z;
    ]

    let mul8 = [
      imul8_rr_x_y_z;
    ]

    let fmul = [
      fmul_rr_x_y_z;
      fmul_rf32_x_y_z;
      fmul_rf64_x_y_z;
    ]

    let mulh = [
      imul_rr_high_x_y_z;
      imul_ri_high_x_y_z;
    ]

    let mulh8 = [
      imul8_rr_high_x_y_z;
      imul8_ri_high_x_y_z;
    ]

    let umulh = [
      mul_rr_high_x_y_z;
      mul_ri_high_x_y_z;
    ]

    let umulh8 = [
      mul8_rr_high_x_y_z;
      mul8_ri_high_x_y_z;
    ]

    let div = [
      idiv_rr_x_y_z;
    ]

    let fdiv = [
      fdiv_rr_x_y_z;
      fdiv_rf32_x_y_z;
      fdiv_rf64_x_y_z;
    ]

    let div8 = [
      idiv8_rr_x_y_z;
    ]

    let rem = [
      idiv_rem_rr_x_y_z;
    ]

    let rem8 = [
      idiv8_rem_rr_x_y_z;
    ]

    let urem = [
      div_rem_rr_x_y_z;
    ]

    let urem8 = [
      div8_rem_rr_x_y_z;
    ]

    let setcc_test ?(neg = false) () = [
      setcc_rr_test_x_y_z ~neg;
      setcc_ri_test_x_y_z ~neg;
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

    let sel cc = [
      sel_rrrr_x_y_z cc;
      sel_rirr_x_y_z cc;
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

    let neg = [
      neg_r_x_y;
      neg_i_x_y;
    ]

    let fneg = [
      fneg_r_x_y;
      fneg_fp32_x_y;
      fneg_fp64_x_y;
    ]

    let not_ = [
      not_r_x_y;
      not_i_x_y;
    ]

    let clz = [
      clz_r_x_y;
    ]

    let clz8 = [
      clz8_r_x_y;
    ]

    let ctz = [
      ctz_r_x_y;
    ]

    let ctz8 = [
      ctz8_r_x_y;
    ]

    let popcnt = [
      popcnt_r_x_y;
    ]

    let popcnt8 = [
      popcnt8_r_x_y;
    ]

    let sext = [
      sext_rr_x_y;
      sext_ri_x_y;
    ]

    let zext = [
      move_rr_x_y;
      move_ri_x_y;
    ]

    let fext ty = [
      fext_rr_x_y ty;
      fext_rf32_x_y ty;
      fext_rf64_x_y ty;
    ]

    let fibits ty = [
      fibits_rr_x_y ty;
      fibits_ri_x_y ty;
    ]

    let ftosi tf ti = [
      ftosi_rr_x_y tf ti;
      ftosi_rf32_x_y ti;
      ftosi_rf64_x_y ti;
    ]

    let ftoui tf ti = [
      ftoui_rr_x_y tf ti;
      ftoui_rf32_x_y ti;
      ftoui_rf64_x_y ti;
    ]

    let ftrunc ty = [
      ftrunc_rr_x_y ty;
      ftrunc_rf32_x_y ty;
      ftrunc_rf64_x_y ty;
    ]

    let ifbits ty = [
      ifbits_rr_x_y ty;
      ifbits_rf32_x_y ty;
      ifbits_rf64_x_y ty;
    ]

    let itrunc ty = [
      itrunc_rr_x_y ty;
      itrunc_ri_x_y ty;
    ]

    let sitof ti tf = [
      sitof_rr_x_y ti tf;
      sitof_ri_x_y ti tf;
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

    let br_test ?(neg = false) () = [
      jcc_rr_test_x_y ~neg;
      jcc_ri_test_x_y ~neg;
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

    let add_mul_lea_tbl = [
      `i16, i16 0,  i16 1,  i16 2,  i16 3,  i16 4,  i16 8;
      `i32, i32 0l, i32 1l, i32 2l, i32 3l, i32 4l, i32 8l;
      `i64, i64 0L, i64 1L, i64 2L, i64 3L, i64 4L, i64 8L;
    ]

    (* x = add (add y (mul z i)) w => lea x, [y+z*i+w]

       where i \in {1,2,4,8} and w is a constant

       x = add (add y (lsl z i)) w => lea x, [y+z*(1<<i)+w]

       where i \in {0,1,2,3} and w is a constant
    *)
    let add_mul_lea_imm =
      add_mul_lea_tbl >* fun (ty, zero, one, two, three, four, eight) ->
        let ty' = bty ty in [
          (* x = add (add y (mul z i)) w *)
          move x (add ty' (add ty' y (mul ty' z one)) w) => add_mul_rr_scale_imm_x_y_z_w 1;
          move x (add ty' (add ty' y (mul ty' z two)) w) => add_mul_rr_scale_imm_x_y_z_w 2;
          move x (add ty' (add ty' y (mul ty' z four)) w) => add_mul_rr_scale_imm_x_y_z_w 4;
          move x (add ty' (add ty' y (mul ty' z eight)) w) => add_mul_rr_scale_imm_x_y_z_w 8;
          (* x = add y (add (mul z i) w) *)
          move x (add ty' y (add ty' (mul ty' z one) w)) => add_mul_rr_scale_imm_x_y_z_w 1;
          move x (add ty' y (add ty' (mul ty' z two) w)) => add_mul_rr_scale_imm_x_y_z_w 2;
          move x (add ty' y (add ty' (mul ty' z four) w)) => add_mul_rr_scale_imm_x_y_z_w 4;
          move x (add ty' y (add ty' (mul ty' z eight) w)) => add_mul_rr_scale_imm_x_y_z_w 8;
          (* x = add (add y (lsl z i)) w *)
          move x (add ty' (add ty' y (lsl_ ty z zero)) w) => add_mul_rr_scale_imm_x_y_z_w 1;
          move x (add ty' (add ty' y (lsl_ ty z one)) w) => add_mul_rr_scale_imm_x_y_z_w 2;
          move x (add ty' (add ty' y (lsl_ ty z two)) w) => add_mul_rr_scale_imm_x_y_z_w 4;
          move x (add ty' (add ty' y (lsl_ ty z three)) w) => add_mul_rr_scale_imm_x_y_z_w 8;
          (* x = add y (add (lsl z i) w) *)
          move x (add ty' y (add ty' (lsl_ ty z zero) w)) => add_mul_rr_scale_imm_x_y_z_w 1;
          move x (add ty' y (add ty' (lsl_ ty z one) w)) => add_mul_rr_scale_imm_x_y_z_w 2;
          move x (add ty' y (add ty' (lsl_ ty z two) w)) => add_mul_rr_scale_imm_x_y_z_w 4;
          move x (add ty' y (add ty' (lsl_ ty z three) w)) => add_mul_rr_scale_imm_x_y_z_w 8;
        ]

    (* x = sub (add y (mul z i)) w => lea x, [y+z*i-w]

       where i \in {1,2,4,8} and w is a constant

       x = sub (add y (lsl z i)) w => lea x, [y+z*(1<<i)-w]

       where i \in {0,1,2,3} and w is a constant
    *)
    let add_mul_lea_neg_imm =
      add_mul_lea_tbl >* fun (ty, zero, one, two, three, four, eight) ->
        let ty' = bty ty in [
          (* x = sub (add y (mul z i)) w *)
          move x (sub ty' (add ty' y (mul ty' z one)) w) => add_mul_rr_scale_neg_imm_x_y_z_w 1;
          move x (sub ty' (add ty' y (mul ty' z two)) w) => add_mul_rr_scale_neg_imm_x_y_z_w 2;
          move x (sub ty' (add ty' y (mul ty' z four)) w) => add_mul_rr_scale_neg_imm_x_y_z_w 4;
          move x (sub ty' (add ty' y (mul ty' z eight)) w) => add_mul_rr_scale_neg_imm_x_y_z_w 8;
          (* x = add y (sub (mul z i) w) *)
          move x (add ty' y (sub ty' (mul ty' z one) w)) => add_mul_rr_scale_neg_imm_x_y_z_w 1;
          move x (add ty' y (sub ty' (mul ty' z two) w)) => add_mul_rr_scale_neg_imm_x_y_z_w 2;
          move x (add ty' y (sub ty' (mul ty' z four) w)) => add_mul_rr_scale_neg_imm_x_y_z_w 4;
          move x (add ty' y (sub ty' (mul ty' z eight) w)) => add_mul_rr_scale_neg_imm_x_y_z_w 8;
          (* x = sub (add y (lsl z i)) w *)
          move x (sub ty' (add ty' y (lsl_ ty z zero)) w) => add_mul_rr_scale_neg_imm_x_y_z_w 1;
          move x (sub ty' (add ty' y (lsl_ ty z one)) w) => add_mul_rr_scale_neg_imm_x_y_z_w 2;
          move x (sub ty' (add ty' y (lsl_ ty z two)) w) => add_mul_rr_scale_neg_imm_x_y_z_w 4;
          move x (sub ty' (add ty' y (lsl_ ty z three)) w) => add_mul_rr_scale_neg_imm_x_y_z_w 8;
          (* x = add y (sub (lsl z i) w) *)
          move x (add ty' y (sub ty' (lsl_ ty z zero) w)) => add_mul_rr_scale_neg_imm_x_y_z_w 1;
          move x (add ty' y (sub ty' (lsl_ ty z one) w)) => add_mul_rr_scale_neg_imm_x_y_z_w 2;
          move x (add ty' y (sub ty' (lsl_ ty z two) w)) => add_mul_rr_scale_neg_imm_x_y_z_w 4;
          move x (add ty' y (sub ty' (lsl_ ty z three) w)) => add_mul_rr_scale_neg_imm_x_y_z_w 8;
        ]

    (* x = add y (mul z i) => lea x, [y+z*i]

       where i \in {1,2,4,8}

       x = add y (lsl z i) => lea x, [y+z*(1<<i)]

       where i \in {0,1,2,3}
    *)
    let add_mul_lea =
      add_mul_lea_tbl >* fun (ty, zero, one, two, three, four, eight) ->
        let ty' = bty ty in [
          (* x = add y (mul z i) *)
          move x (add ty' y (mul ty' z one)) => add_mul_rr_scale_x_y_z 1;
          move x (add ty' y (mul ty' z two)) => add_mul_rr_scale_x_y_z 2;
          move x (add ty' y (mul ty' z four)) => add_mul_rr_scale_x_y_z 4;
          move x (add ty' y (mul ty' z eight)) => add_mul_rr_scale_x_y_z 8;
          (* x = add y (lsl z i) *)
          move x (add ty' y (lsl_ ty z zero)) => add_mul_rr_scale_x_y_z 1;
          move x (add ty' y (lsl_ ty z one)) => add_mul_rr_scale_x_y_z 2;
          move x (add ty' y (lsl_ ty z two)) => add_mul_rr_scale_x_y_z 4;
          move x (add ty' y (lsl_ ty z three)) => add_mul_rr_scale_x_y_z 8;
        ]

    (* x = add y, z *)
    let add_basic = [
      move x (add `i8  y z) =>* Group.add;
      move x (add `i16 y z) =>* Group.add;
      move x (add `i32 y z) =>* Group.add;
      move x (add `i64 y z) =>* Group.add;
      move x (add `f32 y z) =>* Group.add;
      move x (add `f64 y z) =>* Group.add;
    ]

    (* x = sub y z *)
    let sub_basic = [
      move x (sub `i8  y z) =>* Group.sub;
      move x (sub `i16 y z) =>* Group.sub;
      move x (sub `i32 y z) =>* Group.sub;
      move x (sub `i64 y z) =>* Group.sub;
      move x (sub `f32 y z) =>* Group.sub;
      move x (sub `f64 y z) =>* Group.sub;
    ]

    (* x = and y, z *)
    let and_basic = [
      move x (and_ `i8  y z) =>* Group.and_;
      move x (and_ `i16 y z) =>* Group.and_;
      move x (and_ `i32 y z) =>* Group.and_;
      move x (and_ `i64 y z) =>* Group.and_;
    ]

    (* x = or y, z *)
    let or_basic = [
      move x (or_ `i8  y z) =>* Group.or_;
      move x (or_ `i16 y z) =>* Group.or_;
      move x (or_ `i32 y z) =>* Group.or_;
      move x (or_ `i64 y z) =>* Group.or_;
    ]

    (* x = xor y, z *)
    let xor_basic = [
      move x (xor `i8  y z) =>* Group.xor;
      move x (xor `i16 y z) =>* Group.xor;
      move x (xor `i32 y z) =>* Group.xor;
      move x (xor `i64 y z) =>* Group.xor;
    ]

    (* x = lsl y, z *)
    let lsl_basic = [
      move x (lsl_ `i8  y z) =>* Group.lsl_;
      move x (lsl_ `i16 y z) =>* Group.lsl_;
      move x (lsl_ `i32 y z) =>* Group.lsl_;
      move x (lsl_ `i64 y z) =>* Group.lsl_;
    ]

    (* x = lsr y, z *)
    let lsr_basic = [
      move x (lsr_ `i8  y z) =>* Group.lsr_;
      move x (lsr_ `i16 y z) =>* Group.lsr_;
      move x (lsr_ `i32 y z) =>* Group.lsr_;
      move x (lsr_ `i64 y z) =>* Group.lsr_;
    ]

    (* x = asr y, z *)
    let asr_basic = [
      move x (asr_ `i8  y z) =>* Group.asr_;
      move x (asr_ `i16 y z) =>* Group.asr_;
      move x (asr_ `i32 y z) =>* Group.asr_;
      move x (asr_ `i64 y z) =>* Group.asr_;
    ]

    (* x = rol y, z *)
    let rol_basic = [
      move x (rol `i8  y z) =>* Group.rol;
      move x (rol `i16 y z) =>* Group.rol;
      move x (rol `i32 y z) =>* Group.rol;
      move x (rol `i64 y z) =>* Group.rol;
    ]

    (* x = ror y, z *)
    let ror_basic = [
      move x (ror `i8  y z) =>* Group.ror;
      move x (ror `i16 y z) =>* Group.ror;
      move x (ror `i32 y z) =>* Group.ror;
      move x (ror `i64 y z) =>* Group.ror;
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
        ]

    (* x = mul y, z *)
    let mul_basic = [
      move x (mul `i8  y z) =>* Group.mul8;
      move x (mul `i16 y z) =>* Group.mul;
      move x (mul `i32 y z) =>* Group.mul;
      move x (mul `i64 y z) =>* Group.mul;
      move x (mul `f64 y z) =>* Group.fmul;
      move x (mul `f64 y z) =>* Group.fmul;
    ]

    (* x = mulh y, z *)
    let mulh_basic = [
      move x (mulh `i8  y z) =>* Group.mulh8;
      move x (mulh `i16 y z) =>* Group.mulh;
      move x (mulh `i32 y z) =>* Group.mulh;
      move x (mulh `i64 y z) =>* Group.mulh;
    ]

    (* x = umulh y, z *)
    let umulh_basic = [
      move x (umulh `i8  y z) =>* Group.umulh8;
      move x (umulh `i16 y z) =>* Group.umulh;
      move x (umulh `i32 y z) =>* Group.umulh;
      move x (umulh `i64 y z) =>* Group.umulh;
    ]

    (* x = div y, z *)
    let div_basic = [
      move x (div `i8  y z) =>* Group.div8;
      move x (div `i16 y z) =>* Group.div;
      move x (div `i32 y z) =>* Group.div;
      move x (div `i64 y z) =>* Group.div;
      move x (div `f64 y z) =>* Group.fdiv;
      move x (div `f64 y z) =>* Group.fdiv;
    ]

    (* x = rem y, z *)
    let rem_basic = [
      move x (rem `i8  y z) =>* Group.rem8;
      move x (rem `i16 y z) =>* Group.rem;
      move x (rem `i32 y z) =>* Group.rem;
      move x (rem `i64 y z) =>* Group.rem;
    ]

    (* x = urem y, z *)
    let urem_basic = [
      move x (urem `i8  y z) =>* Group.urem8;
      move x (urem `i16 y z) =>* Group.urem;
      move x (urem `i32 y z) =>* Group.urem;
      move x (urem `i64 y z) =>* Group.urem;
    ]

    (* x = y == 0
       x = y != 0
    *)
    let setcc_zero =
      [`i8,  i8  0;
       `i16, i16 0;
       `i32, i32 0l;
       `i64, i64 0L;
      ] >* fun (ty, zero) ->
        let ty' = (ty :> Type.basic) in [
          move x (ne ty' (and_ ty y z) zero) =>* Group.setcc_test (); (* x = (y & z) != 0 *)
          move x (eq ty' (and_ ty y z) zero) =>* Group.setcc_test () ~neg:true; (* x = (y & z) == 0 *)
          move x (eq ty' y zero) => setcc_r_zero_x_y; (* x = y == 0 *)
          move x (ne ty' y zero) => setcc_r_zero_x_y ~neg:true; (* x = y != 0 *)
          move x (slt ty y zero) => setcc_r_less_than_zero_x_y; (* x = y <$ 0 *)
          move x (sge ty y zero) => setcc_r_less_than_zero_x_y ~neg:true; (* x = y >=$ 0 *)
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

    (* x = sel (cmp y z) yes no *)
    let sel_ibasic =
      [`i8; `i16; `i32; `i64] >* fun ty ->
        let ty' = bty ty in [
          (* Equality *)
          move x (sel ty' (eq ty' y z) yes no) =>* Group.sel Ce;
          move x (sel ty' (ne ty' y z) yes no) =>* Group.sel Cne;
          (* Unsigned *)
          move x (sel ty' (lt ty' y z) yes no) =>* Group.sel Cb;
          move x (sel ty' (le ty' y z) yes no) =>* Group.sel Cbe;
          move x (sel ty' (gt ty' y z) yes no) =>* Group.sel Ca;
          move x (sel ty' (ge ty' y z) yes no) =>* Group.sel Cae;
          (* Signed *)
          move x (sel ty' (slt ty y z) yes no) =>* Group.sel Cl;
          move x (sel ty' (sle ty y z) yes no) =>* Group.sel Cle;
          move x (sel ty' (sgt ty y z) yes no) =>* Group.sel Cg;
          move x (sel ty' (sge ty y z) yes no) =>* Group.sel Cge;
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

    (* x = neg y *)
    let neg_basic = [
      move x (neg `i8  y) =>* Group.neg;
      move x (neg `i16 y) =>* Group.neg;
      move x (neg `i32 y) =>* Group.neg;
      move x (neg `i64 y) =>* Group.neg;
      move x (neg `f32 y) =>* Group.fneg;
      move x (neg `f64 y) =>* Group.fneg;
    ]

    (* x = not y *)
    let not_basic = [
      move x (not_ `i8  y) =>* Group.not_;
      move x (not_ `i16 y) =>* Group.not_;
      move x (not_ `i32 y) =>* Group.not_;
      move x (not_ `i64 y) =>* Group.not_;
    ]

    (* x = clz y *)
    let clz_basic = [
      move x (clz `i8  y) =>* Group.clz8;
      move x (clz `i16 y) =>* Group.clz;
      move x (clz `i32 y) =>* Group.clz;
      move x (clz `i64 y) =>* Group.clz;
    ]

    (* x = ctz y *)
    let ctz_basic = [
      move x (ctz `i8  y) =>* Group.ctz8;
      move x (ctz `i16 y) =>* Group.ctz;
      move x (ctz `i32 y) =>* Group.ctz;
      move x (ctz `i64 y) =>* Group.ctz;
    ]

    (* x = popcnt y *)
    let popcnt_basic = [
      move x (popcnt `i8  y) =>* Group.popcnt8;
      move x (popcnt `i16 y) =>* Group.popcnt;
      move x (popcnt `i32 y) =>* Group.popcnt;
      move x (popcnt `i64 y) =>* Group.popcnt;
    ]

    (* x = sext y *)
    let sext_basic = [
      move x (sext `i8  y) =>* Group.move_ri;
      move x (sext `i16 y) =>* Group.sext;
      move x (sext `i32 y) =>* Group.sext;
      move x (sext `i64 y) =>* Group.sext;
    ]

    (* x = zext y *)
    let zext_basic = [
      move x (zext `i8  y) =>* Group.move_ri;
      move x (zext `i16 y) =>* Group.zext;
      move x (zext `i32 y) =>* Group.zext;
      move x (zext `i64 y) =>* Group.zext;
    ]

    (* x = fext y *)
    let fext_basic = [
      move x (fext `f32 y) =>* Group.fext `f32;
      move x (fext `f64 y) =>* Group.fext `f64;
    ]

    (* x = fibits y *)
    let fibits_basic = [
      move x (fibits `f32 y) =>* Group.fibits `f32;
      move x (fibits `f64 y) =>* Group.fibits `f64;
    ]

    (* x = ftosi y *)
    let ftosi_basic =
      [`i8; `i16; `i32; `i64] >* fun ty ->
        let ty' = (ty :> Type.imm) in [
          move x (ftosi `f64 ty' y) =>* Group.ftosi `f64 ty;
          move x (ftosi `f32 ty' y) =>* Group.ftosi `f32 ty;
        ]

    (* x = ftoui y *)
    let ftoui_basic =
      [`i8; `i16; `i32; `i64] >* fun ty ->
        let ty' = (ty :> Type.imm) in [
          move x (ftoui `f64 ty' y) =>* Group.ftoui `f64 ty;
          move x (ftoui `f32 ty' y) =>* Group.ftoui `f32 ty;
        ]

    (* x = ftrunc y *)
    let ftrunc_basic = [
      move x (ftrunc `f32 y) =>* Group.ftrunc `f32;
      move x (ftrunc `f64 y) =>* Group.ftrunc `f64;
    ]

    (* x = ifbits y *)
    let ifbits_basic = [
      move x (ifbits `i32 y) =>* Group.ifbits `i64;
      move x (ifbits `i64 y) =>* Group.ifbits `i64;
    ]

    (* x = itrunc y *)
    let itrunc_basic =
      [`i8; `i16; `i32; `i64] >* fun ty -> [
          move x (itrunc ty y) =>* Group.itrunc ty;
        ]

    (* x = sitof y *)
    let sitof_basic =
      [`i8; `i16; `i32; `i64] >* fun ty -> [
          move x (sitof ty `f32 y) =>* Group.sitof ty `f32;
          move x (sitof ty `f64 y) =>* Group.sitof ty `f64;
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

    (* br ((x & y) == 0), yes, no
       br ((x & y) != 0), yes, no
       br (x == 0), yes, no
       br (x != 0), yes, no
    *)
    let br_zero =
      [`i8,  i8  0;
       `i16, i16 0;
       `i32, i32 0l;
       `i64, i64 0L;
      ] >* fun (ty, zero) ->
        let ty' = (ty :> Type.basic) in [
          (* Test two operands. *)
          br (ne ty' (and_ ty x y) zero) yes no =>* Group.br_test ();
          br (eq ty' (and_ ty x y) zero) yes no =>* Group.br_test () ~neg:true;
          (* Test against self for ZF. *)
          br (eq ty' x zero) yes no => jcc_r_zero_x;
          br (ne ty' x zero) yes no => jcc_r_zero_x ~neg:true;
          (* Test against self for SF. *)
          br (slt ty x zero) yes no => jcc_r_less_than_zero_x;
          br (sge ty x zero) yes no => jcc_r_less_than_zero_x ~neg:true;
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

    (* sw x tbl *)
    let sw_basic = [
      sw `i8  x y => jmp_tbl_x_y;
      sw `i16 x y => jmp_tbl_x_y;
      sw `i32 x y => jmp_tbl_x_y;
      sw `i64 x y => jmp_tbl_x_y;
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
    add_mul_lea_imm @
    add_mul_lea_neg_imm @
    add_mul_lea @
    add_basic @
    sub_basic @
    and_basic @
    or_basic @
    xor_basic @
    lsl_basic @
    lsr_basic @
    asr_basic @
    rol_basic @
    ror_basic @
    mul_lea @
    mul_basic @
    mulh_basic @
    umulh_basic @
    div_basic @
    rem_basic @
    urem_basic @
    setcc_zero @
    setcc_ibasic @
    setcc_fbasic @
    sel_ibasic @
    load_add @
    load_basic @
    neg_basic @
    not_basic @
    clz_basic @
    ctz_basic @
    popcnt_basic @
    sext_basic @
    zext_basic @
    fext_basic @
    fibits_basic @
    ftosi_basic @
    ftoui_basic @
    ftrunc_basic @
    ifbits_basic @
    itrunc_basic @
    sitof_basic @
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
    sw_basic @
    hlt @
    ret
end
