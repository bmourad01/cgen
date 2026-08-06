open Core

module Bv = Cgen_utils.Bv
module R = X86_amd64_common.Reg
module Rv = X86_amd64_common.Regvar
module Insn = X86_amd64_common.Insn
module Float32 = Cgen_utils.Float32

let (>*) x f = List.bind x ~f

let ity ty = (ty :> Type.imm)
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

(* Promote i8/i16 register operand widths to i32 for truncation-invariant
   ops (e.g. mov, add, sub, neg, not, and, or, xor).

   Writing 32 bits implicitly zero-extends to 64 bits, breaking the false
   dependency that 8-or-16-bit partial writes would carry on the prior
   full-register value.

   The low N bits of the result are identical to the 8-or-16-bit computation,
   which is all that downstream consumers will read. Narrower consumers either
   access 8 or 16 bits directly or issue an explicit zero/sign extension.

   `i64` must stay `i64` (we'd lose the high 32 bits otherwise), and FP types
   are unaffected.
*)
let promote_narrow_ty = function
  | `i8 | `i16 -> `i32
  | ty -> ty

(* True if `x` fits in a zero-extended 32-bit encoding. *)
let fits_int32 x =
  let open Int64 in
  x >= 0xFFFFFFFF80000000L &&
  x <= 0xFFFFFFFFL

(* True if `x` fits in a sign-extended 32-bit encoding. *)
let fits_sext32 x =
  let open Int64 in
  x >= -0x80000000L &&
  x <= 0x7FFFFFFFL

(* True if `x` can be encoded as an imm32 for an instruction with
   operand type `ty`.

   For 64-bit operands the CPU sign-extends imm32, so only the sext32
   range is valid; for narrower operands the full 32-bit bit-pattern
   is used as-is.
*)
let fits_imm ty x = match ty with
  | `i64 -> fits_sext32 x
  | _    -> fits_int32 x

let fits_int32_neg x =
  let open Int64 in
  x < 0L && x >= 0xFFFFFFFF80000000L

let fits_int32_pos x =
  let open Int64 in
  x > 0L && x <= 0x7FFFFFFFL

(* True iff `x`'s high 32 bits are zero, i.e. it is representable in the low 32
   bits with a zero upper half. This is the condition under which narrowing a
   64-bit operation to its 32-bit form is sound: the 32-bit form zero-extends
   the result into the full register, which matches the 64-bit result only when
   the upper half was going to be zero anyway. (Unlike `fits_int32`, this
   excludes negatives, whose sign-extension sets the upper half.) *)
let fits_uint32 x =
  let open Int64 in
  x >= 0L && x <= 0xFFFFFFFFL

let can_lea_ty = function
  | `i16 | `i32 | `i64 -> true
  | _ -> false

let compare_u a b =
  Int64.(compare (a lxor min_value) (b lxor min_value))

let lt_u a b = compare_u a b <  0 [@@inline] [@@ocaml.warning "-32"]
let le_u a b = compare_u a b <= 0 [@@inline] [@@ocaml.warning "-32"]
let gt_u a b = compare_u a b >  0 [@@inline] [@@ocaml.warning "-32"]
let ge_u a b = compare_u a b >= 0 [@@inline] [@@ocaml.warning "-32"]

let array_of_list_map l ~f = match l with
  | [] -> [||]
  | [x] -> [|f x|]
  | x :: rest ->
    let len = List.length rest + 1 in
    let a = Array.create ~len (f x) in
    List.iteri rest ~f:(fun i x -> a.(i + 1) <- f x);
    a

(* pre: `tbl` is non-empty and sorted

   NB: this function is deliberately naiive, and we expect that
   the `Lower_switch` pass has been run beforehand
*)
let adjust_table d = function
  | [] -> assert false
  | (lowest, l1) :: rest ->
    let lowest = Bv.to_int64 lowest in
    let highest = ref lowest in
    let[@tail_mod_cons] rec go p = function
      | [] -> []
      | (v, l) :: rest ->
        let v = Bv.to_int64 v in
        highest := v;
        (* `diff` is the distance from the previous index `p`
           to the current one `v`, so we need to pad that gap
           with the default label.  *)
        let diff = Int64.(v - p) in
        let[@tail_mod_cons] rec with_pad i =
          if lt_u i diff
          then d :: with_pad (Int64.succ i)
          else l :: go (Int64.succ v) rest in
        with_pad 0L in
    let tbl' = l1 :: go (Int64.succ lowest) rest in
    tbl', lowest, !highest

let (let@) f x = f x

module Make(C : Context_intf.S) : sig
  val rules : (Rv.t, Insn.t) Isel_rewrite.Rule(C).t list
end = struct
  open C.Syntax
  open Isel_rewrite.Rule(C)
  open X86_amd64_common.Insn

  module P = Isel_rewrite.Pattern
  module S = Isel_rewrite.Subst

  let w = P.var "w"
  let x = P.var "x"
  let y = P.var "y"
  let z = P.var "z"
  let yes = P.var "yes"
  let no = P.var "no"

  let (@!!) a b = !!(a @ b) [@@inline]

  let fresh_reg = C.Var.fresh >>| Rv.var

  let fresh_label_addr =
    let+ l = C.Label.fresh in
    l, Albl (l, 0)

  (* If `z` fits in a sign-extended imm32 for operands of type `ty`, pass it
     directly as `Oimm`, otherwise spill it into a fresh 64-bit temporary and
     pass that.

     The spill path is only reachable when ty = `i64. For narrower types,
     `fits_imm` delegates to `fits_int32`, which accepts the full 32-bit
     range, so every valid immediate for those types passes the guard.
  *)
  let with_imm ty z zt f =
    if fits_imm ty z then f (Oimm (z, zt)) else
      let* tmp = C.Var.fresh >>| Rv.var in
      let+ result = f (Oreg (tmp, `i64)) in
      List.cons (I.mov (Oreg (tmp, `i64)) (Oimm (z, zt))) result

  let extbh ?(signed = false) x xt' xt f =
    let i = if signed then I.movsx else I.movzx in
    let suffix = match xt with
      | `i8 | `i16 -> [i (Oreg (x, xt')) (Oreg (x, xt))]
      | _ -> [] in
    f suffix

  let xor_gpr_self x ty =
    (* `xor r32, r32` is a shorter encoding than `xor r64, r64` and still
       zero-clears all 64 bits of the GPR. For i8/i16, promoting to i32 also
       breaks the false dep a partial write would carry. *)
    let ty = match ty with
      | `i64 -> `i32
      | ty -> promote_narrow_ty ty in
    let x = Oreg (x, ty) in
    I.xor x x

  let cwd_cdq_cqo (ty : Type.basic) = match ty with
    | `i16 -> I.cwd
    | `i32 -> I.cdq
    | `i64 -> I.cqo
    | `i8 | #Type.fp -> assert false

  let mov_typed xt dst src = match xt with
    | #Type.imm -> I.mov   dst src
    | `f32      -> I.movss dst src
    | `f64      -> I.movsd dst src

  (* Load into a GPR, promoting i8/i16 destinations to i32 via movzx to
     avoid a partial-register false dependency on the old value of the
     64-bit register. *)
  let load_typed xt x addr = match (xt : Type.basic) with
    | `i8 | `i16  -> I.movzx (Oreg (x, `i32)) addr
    | `i32 | `i64 -> I.mov   (Oreg (x, xt)) addr
    | `f32        -> I.movss (Oreg (x, xt)) addr
    | `f64        -> I.movsd (Oreg (x, xt)) addr

  (* Fused sext-of-load: sign-extend from the narrow memory type `zt` into
     `xt` in a single instruction. Similarly to `load_typed`, we promote
     the width to avoid a false dependency. *)
  let sext_load_typed xt zt x addr = match xt, zt with
    | `i64, `i32 ->
      I.movsxd (Oreg (x, `i64)) addr
    | (`i16 | `i32 | `i64), (`i8 | `i16) ->
      let xt' = promote_narrow_ty xt in
      I.movsx (Oreg (x, xt')) addr
    | _, _ -> assert false

  (* Same as `load_typed`, but narrowed to `Type.imm`. *)
  let zext_load_typed zt x addr = match zt with
    | `i8 | `i16 -> I.movzx (Oreg (x, `i32)) addr
    | `i32       -> I.mov   (Oreg (x, `i32)) addr
    | `i64       -> I.mov   (Oreg (x, `i64)) addr

  (* Load a symbol's address into a GPR. We go through the `Asym` memory
     operand (RIP-relative) rather than `Osym` (a bare absolute symbol) so
     the emitted `lea` is position-independent: `lea dst, [rip + sym]`
     instead of `lea dst, sym` (an `R_X86_64_32S` relocation, which the
     linker rejects when building a PIE). *)
  let lea_sym dst s o = I.lea (Oreg (dst, `i64)) (Omem (Asym (s, o), `i64))

  (* Check that the "built-in" symbol offset would fit in the signed imm32
     of a displacement. *)
  let sym_disp_fits o = fits_sext32 (Int64.of_int o)

  (* Rule callbacks. *)

  let move_rr_x_y ?(zx = false) env = [%rule
    let S.Treg (x, xt) = env.!["x"] in
    let S.Treg (y, yt) = env.!["y"] in
    (* This should be handled by the matching logic, but we'll put it
       here just in case. *)
    guard (not (Rv.equal x y));
    match xt, yt with
    | (`i64 | `i32), `i32 when zx ->
      (* Implicit zero-extension. *)
      [I.mov (Oreg (x, yt)) (Oreg (y, yt))]
    (* Assume zero-extension is desired. There is no `movzx r64, r32`, since
       writing a 32-bit register already clears the upper half, so widening
       from i32 is a plain 32-bit mov. *)
    | `i64, `i32 -> [I.mov (Oreg (x, `i32)) (Oreg (y, `i32))]
    | (#Type.imm as xi), (#Type.imm as yi)
      when Type.sizeof_imm xi > Type.sizeof_imm yi ->
      let xt' = match xt, yt with
        | `i64, (`i16 | `i8) -> `i32
        | _ -> xt in
      [I.movzx (Oreg (x, xt')) (Oreg (y, yt))]
    | #Type.imm, #Type.imm ->
      (* Assume the width of the destination register, but promote i8/i16
         to i32 to avoid a partial-register write. *)
      let xt' = promote_narrow_ty xt in
      [I.mov (Oreg (x, xt')) (Oreg (y, xt'))]
    | `f32, `f32 ->
      [I.movss (Oreg (x, xt)) (Oreg (y, yt))]
    | `f64, `f64 ->
      [I.movsd (Oreg (x, xt)) (Oreg (y, yt))]
    | _ -> fail
  ]

  let move_ri_x_y ?(zx = false) env = [%rule
    let S.Treg (x, xt) = env.!["x"] in
    let S.Timm (y, yt) = env.!["y"] in
    guard (zx || Type.equal_basic xt (bty yt));
    if Bv.(y = zero) then
      [xor_gpr_self x xt]
    else
      let y = Bv.to_int64 y in
      let ty = match yt with
        | `i64 when fits_int32_pos y -> `i32
        | `i8 | `i16 -> `i32
        | _ -> yt in
      [I.mov (Oreg (x, bty ty)) (Oimm (y, ty))]
  ]

  let move_rb_x_y env = [%rule
    let S.Treg (x, xt) = env.!["x"] in
    let (#Type.imm as xti) = xt in
    let S.Tbool y = env.!["y"] in
    if y then
      let xt' = promote_narrow_ty xt in
      let xti' = match xti with
        | `i8 | `i16 -> `i32
        | t -> t in
      [I.mov (Oreg (x, xt')) (Oimm (1L, xti'))]
    else [xor_gpr_self x xt]
  ]

  let move_rsym_x_y env = [%rule
    let S.Treg (x, xt) = env.!["x"] in
    let S.Tsym (s, o)     = env.!["y"] in
    if sym_disp_fits o then
      [I.lea (Oreg (x, xt)) (Omem (Asym (s, o), `i64))]
    else
      let@ oo = with_imm `i64 (Int64.of_int o) `i64 in [
        I.lea (Oreg (x, `i64)) (Omem (Asym (s, 0), `i64));
        I.add (Oreg (x, `i64)) oo
      ]
  ]

  let move_rf32_x_y env = [%rule
    let S.Treg (x, xt) = env.!["x"] in
    guard (Type.equal_basic xt `f32);
    let S.Tf32 c = env.!["y"] in
    let* l, addr = fresh_label_addr in [
      I.movss (Oreg (x, xt)) (Omem (addr, mty `f32));
      I.fp32 l c
    ]
  ]

  let move_rf64_x_y env = [%rule
    let S.Treg (x, xt) = env.!["x"] in
    guard (Type.equal_basic xt `f64);
    let S.Tf64 c = env.!["y"] in
    let* l, addr = fresh_label_addr in [
      I.movsd (Oreg (x, xt)) (Omem (addr, mty `f64));
      I.fp64 l c
    ]
  ]

  (* `x = y` for register/immediate sources (used by plain moves and `zext`),
     dispatching on the source form. *)
  let move_reg_imm ?(zx = false) env = [%rule
    match env.!["y"] with
    | S.Treg _ -> continue (move_rr_x_y ~zx env)
    | S.Timm _ -> continue (move_ri_x_y ~zx env)
    | _ -> fail
  ]

  (* `x = y`, dispatching on the source form (register, immediate, boolean,
     symbol, or fp constant). *)
  let move_unary env = [%rule
    match env.!["y"] with
    | S.Treg _ -> continue (move_rr_x_y env)
    | S.Timm _ -> continue (move_ri_x_y env)
    | S.Tbool _ -> continue (move_rb_x_y env)
    | S.Tsym _ -> continue (move_rsym_x_y env)
    | S.Tf32 _ -> continue (move_rf32_x_y env)
    | S.Tf64 _ -> continue (move_rf64_x_y env)
    | _ -> fail
  ]

  (* `x = flag y`: materialize a flag value into a register, dispatching on
     whether `y` is a computed flag (zero-extended) or a boolean constant. *)
  let flag_to_reg env = [%rule
    match env.!["y"] with
    | S.Treg _ -> continue (move_rr_x_y ~zx:true env)
    | S.Tbool _ -> continue (move_rb_x_y env)
    | _ -> fail
  ]

  let add_mul_rr_scale_x_y_z s env = [%rule
    let S.Treg (x, xt) = env.!["x"] in
    let S.Treg (y, _)  = env.!["y"] in
    let S.Treg (z, _)  = env.!["z"] in
    guard (can_lea_ty xt);
    [I.lea (Oreg (x, xt)) (Omem (Abis (y, z, s), `i64))]
  ]

  let lea_bisd_x_y_z_w neg s env = [%rule
    let S.Treg (x, xt) = env.!["x"] in
    let S.Treg (y, _) = env.!["y"] in
    let S.Treg (z, _) = env.!["z"] in
    let S.Timm (w, _) = env.!["w"] in
    let w = Bv.to_int64 w in
    let nw = if neg then Int64.neg w else w in
    guard (can_lea_ty xt);
    guard ((if neg then fits_int32_neg else fits_int32_pos) nw);
    let w = Int64.to_int32_trunc nw in
    [I.lea (Oreg (x, xt)) (Omem (Abisd (y, z, s, w), `i64))]
  ] [@@specialise]

  let add_mul_rr_scale_imm_x_y_z_w = lea_bisd_x_y_z_w false
  let add_mul_rr_scale_neg_imm_x_y_z_w = lea_bisd_x_y_z_w true

  let add_ri_x_y_z env = [%rule
    let S.Treg (x, xt) = env.!["x"] in
    let S.Treg (y, yt) = env.!["y"] in
    guard (Type.equal_basic xt yt);
    let S.Timm (z, zt) = env.!["z"] in
    let z = Bv.to_int64 z in
    let xt' = promote_narrow_ty xt in
    let zt' = match zt with
      | `i8 | `i16 -> `i32
      | t -> t in
    if Int64.(z = 0L) then
      [I.mov (Oreg (x, xt')) (Oreg (y, xt'))]
    else if not (Rv.equal x y) && fits_int32_pos z && can_lea_ty xt then
      let z = Int64.to_int32_trunc z in
      [I.lea (Oreg (x, xt')) (Omem (Abd (y, z), `i64))]
    else
      let@ oz = with_imm xt' z zt' in
      if Rv.equal x y then
        [I.add (Oreg (x, xt')) oz]
      else [
        I.mov (Oreg (x, xt')) (Oreg (y, xt'));
        I.add (Oreg (x, xt')) oz
      ]
  ]

  let arith_float_rf32 i1 i2 f env = [%rule
    let S.Treg (x, xt) = env.!["x"] in
    let S.Treg (y, yt) = env.!["y"] in
    guard (Type.equal_basic xt yt);
    let S.Tf32 c = env.!["z"] in
    let* l, addr = fresh_label_addr in [
      i1 (Oreg (x, xt)) (Oreg (y, yt));
      i2 (Oreg (x, xt)) (Omem (addr, `f32));
      f l c
    ]
  ] [@@specialise]

  let arith_float_rf64 i1 i2 f env = [%rule
    let S.Treg (x, xt) = env.!["x"] in
    let S.Treg (y, yt) = env.!["y"] in
    guard (Type.equal_basic xt yt);
    let S.Tf64 c = env.!["z"] in
    let* l, addr = fresh_label_addr in [
      i1 (Oreg (x, xt)) (Oreg (y, yt));
      i2 (Oreg (x, xt)) (Omem (addr, `f64));
      f l c
    ]
  ] [@@specialise]

  let arith_float_fr32 i1 i2 f env = [%rule
    let S.Treg (x, xt) = env.!["x"] in
    let S.Tf32 c = env.!["y"] in
    let S.Treg (z, zt) = env.!["z"] in
    guard (Type.equal_basic xt zt);
    let* l, addr = fresh_label_addr in [
      i1 (Oreg (x, xt)) (Omem (addr, `f32));
      i2 (Oreg (x, xt)) (Oreg (z, zt));
      f l c
    ]
  ] [@@specialise]

  let arith_float_fr64 i1 i2 f env = [%rule
    let S.Treg (x, xt) = env.!["x"] in
    let S.Tf64 c = env.!["y"] in
    let S.Treg (z, zt) = env.!["z"] in
    guard (Type.equal_basic xt zt);
    let* l, addr = fresh_label_addr in [
      i1 (Oreg (x, xt)) (Omem (addr, `f64));
      i2 (Oreg (x, xt)) (Oreg (z, zt));
      f l c
    ]
  ] [@@specialise]

  (* `x = add y z`, dispatching on the operand forms. `add` is commutative, so
     the matcher presents both orders and we spell only the canonical one for
     each mixed form. The reg-imm form is shared with the `mul_lea_add_imm`
     structural rule, and the float forms with `sub`, so both delegate. *)
  let add_binop env = [%rule
    let S.Treg (x, xt) = env.!["x"] in
    match env.!["y"], env.!["z"] with
    | S.Treg (y, yt), S.Treg (z, zt) ->
      guard (Type.equal_basic xt yt);
      guard (Type.equal_basic xt zt);
      if Rv.(x <> y) && can_lea_ty xt then
        let xt' = promote_narrow_ty xt in
        [I.lea (Oreg (x, xt')) (Omem (Abis (y, z, S1), `i64))]
      else begin match xt with
        | #Type.imm ->
          let xt' = promote_narrow_ty xt in [
            I.mov (Oreg (x, xt')) (Oreg (y, xt'));
            I.add (Oreg (x, xt')) (Oreg (z, xt'))
          ]
        | `f64 -> [
            I.movsd (Oreg (x, xt)) (Oreg (y, yt));
            I.addsd (Oreg (x, xt)) (Oreg (z, zt))
          ]
        | `f32 -> [
            I.movss (Oreg (x, xt)) (Oreg (y, yt));
            I.addss (Oreg (x, xt)) (Oreg (z, zt))
          ]
      end
    | S.Treg _, S.Timm _ -> continue (add_ri_x_y_z env)
    | S.Treg (y, _), S.Tsym (s, o) ->
      guard (can_lea_ty xt);
      let* tmp = fresh_reg in
      let xt' = promote_narrow_ty xt in [
        I.lea (Oreg (tmp, `i64)) (Omem (Asym (s, o), `i64));
        I.lea (Oreg (x, xt')) (Omem (Abis (y, tmp, S1), `i64))
      ]
    | S.Tsym (s, o), S.Timm (z, _) ->
      guard (can_lea_ty xt);
      let d = Int64.(of_int o + Bv.to_int64 z) in
      guard (fits_sext32 d);
      let xt' = promote_narrow_ty xt in
      [I.lea (Oreg (x, xt')) (Omem (Asym (s, Int64.to_int_trunc d), `i64))]
    | S.Treg _, S.Tf32 _ -> continue (arith_float_rf32 I.movss I.addss I.fp32 env)
    | S.Treg _, S.Tf64 _ -> continue (arith_float_rf64 I.movsd I.addsd I.fp64 env)
    | _ -> fail
  ]

  (* `x = sub y z`. Not commutative, so reg-imm, imm-reg, float reg-const, and
     const-reg forms are spelled explicitly. *)
  let sub_binop env = [%rule
    let S.Treg (x, xt) = env.!["x"] in
    match env.!["y"], env.!["z"] with
    | S.Treg (y, yt), S.Treg (z, zt) ->
      guard (Type.equal_basic xt yt);
      guard (Type.equal_basic xt zt);
      begin match xt with
        | #Type.imm ->
          let xt' = promote_narrow_ty xt in [
            I.mov (Oreg (x, xt')) (Oreg (y, xt'));
            I.sub (Oreg (x, xt')) (Oreg (z, xt'))
          ]
        | `f64 -> [
            I.movsd (Oreg (x, xt)) (Oreg (y, yt));
            I.subsd (Oreg (x, xt)) (Oreg (z, zt))
          ]
        | `f32 -> [
            I.movss (Oreg (x, xt)) (Oreg (y, yt));
            I.subss (Oreg (x, xt)) (Oreg (z, zt))
          ]
      end
    | S.Treg (y, yt), S.Timm (z, zt) ->
      guard (Type.equal_basic xt yt);
      let z = Bv.to_int64 z in
      let nz = Int64.neg z in
      let xt' = promote_narrow_ty xt in
      let zt' = match zt with
        | `i8 | `i16 -> `i32
        | t -> t in
      if Int64.(z = 0L) then
        [I.mov (Oreg (x, xt')) (Oreg (y, xt'))]
      else if not (Rv.equal x y) && fits_int32_neg nz && can_lea_ty xt then
        let z = Int64.to_int32_trunc nz in
        [I.lea (Oreg (x, xt')) (Omem (Abd (y, z), `i64))]
      else
        let@ oz = with_imm xt' z zt' in
        if Rv.equal x y then
          [I.sub (Oreg (x, xt')) oz]
        else [
          I.mov (Oreg (x, xt')) (Oreg (y, xt'));
          I.sub (Oreg (x, xt')) oz
        ]
    | S.Timm (y, yt), S.Treg (z, zt) ->
      guard (Type.equal_basic xt zt);
      let y = Bv.to_int64 y in
      let xt' = promote_narrow_ty xt in
      let yt' = match yt with
        | `i8 | `i16 -> `i32
        | t -> t in [
        I.mov (Oreg (x, xt')) (Oimm (y, yt'));
        I.sub (Oreg (x, xt')) (Oreg (z, xt'))
      ]
    | S.Treg _, S.Tf32 _ -> continue (arith_float_rf32 I.movss I.subss I.fp32 env)
    | S.Treg _, S.Tf64 _ -> continue (arith_float_rf64 I.movsd I.subsd I.fp64 env)
    | S.Tf32 _, S.Treg _ -> continue (arith_float_fr32 I.movss I.subss I.fp32 env)
    | S.Tf64 _, S.Treg _ -> continue (arith_float_fr64 I.movsd I.subsd I.fp64 env)
    | _ -> fail
  ]

  (* `x = y <op> z` for the bitwise binops, dispatching on the form of `z`
     (register or immediate). `i` is the emitter for the chosen encoding. *)
  let bitwise ?(trunc = false) i env = [%rule
    let S.Treg (x, xt) = env.!["x"] in
    let S.Treg (y, _)  = env.!["y"] in
    match env.!["z"] with
    | S.Treg (z, _) ->
      let xt' = promote_narrow_ty xt in [
        I.mov (Oreg (x, xt')) (Oreg (y, xt'));
        i (Oreg (x, xt')) (Oreg (z, xt'))
      ]
    | S.Timm (z, zt) ->
      let z = Bv.to_int64 z in
      let xt', zt' = match xt with
        | `i64 when trunc && fits_uint32 z -> `i32, `i32
        | `i8 | `i16 -> `i32, `i32
        | _ -> xt, zt in
      let@ oz = with_imm xt' z zt' in [
        I.mov (Oreg (x, xt')) (Oreg (y, xt'));
        i (Oreg (x, xt')) oz
      ]
    | _ -> fail
  ] [@@specialise]

  let jmp_lbl_x env = [%rule
    let S.Tlbl x = env.!["x"] in
    [I.jmp (Jlbl x)]
  ]

  let jmp_sym_x env = [%rule
    let S.Tsym (s, o) = env.!["x"] in
    [I.jmp (Jind (Osym (s, o)))]
  ]

  let jmp_r_x env = [%rule
    let S.Treg (x, xt) = env.!["x"] in
    guard (Type.equal_basic xt `i64);
    [I.jmp (Jind (Oreg (x, xt)))]
  ]

  let jmp_i_x env = [%rule
    let S.Timm (x, xt) = env.!["x"] in
    guard (Type.equal_imm xt `i64);
    let* tmp = fresh_reg in
    let x = Bv.to_int64 x in
    let ty = if fits_uint32 x then `i32 else xt in [
      I.mov (Oreg (tmp, bty ty)) (Oimm (x, ty));
      I.jmp (Jind (Oreg (tmp, `i64)))
    ]
  ]

  (* `jmp x`, dispatching on the form of the target `x`. *)
  let jmp_op env = [%rule
    match env.!["x"] with
    | S.Tlbl _ -> continue (jmp_lbl_x env)
    | S.Tsym _ -> continue (jmp_sym_x env)
    | S.Treg _ -> continue (jmp_r_x env)
    | S.Timm _ -> continue (jmp_i_x env)
    | _ -> fail
  ]

  let jcc_r_zero_x ?(neg = false) env = [%rule
    let S.Treg (x, xt) = env.!["x"] in
    let S.Tlbl yes = env.!["yes"] in
    let S.Tlbl no = env.!["no"] in
    let cc = if neg then Cne else Ce in [
      I.test (Oreg (x, xt)) (Oreg (x, xt));
      I.jcc cc yes;
      I.jmp (Jlbl no)
    ]
  ]

  let jcc_r_less_than_zero_x ?(neg = false) env = [%rule
    let S.Treg (x, xt) = env.!["x"] in
    let S.Tlbl yes = env.!["yes"] in
    let S.Tlbl no = env.!["no"] in
    let cc = if neg then Cns else Cs in [
      I.test (Oreg (x, xt)) (Oreg (x, xt));
      I.jcc cc yes;
      I.jmp (Jlbl no)
    ]
  ]

  let jcc_rr_test_x_y ?(neg = false) env = [%rule
    let S.Treg (x, xt) = env.!["x"] in
    let S.Treg (y, yt) = env.!["y"] in
    let S.Tlbl yes = env.!["yes"] in
    let S.Tlbl no = env.!["no"] in
    let cc = if neg then Ce else Cne in [
      I.test (Oreg (x, xt)) (Oreg (y, yt));
      I.jcc cc yes;
      I.jmp (Jlbl no)
    ]
  ]

  let jcc_ri_test_x_y ?(neg = false) env = [%rule
    let S.Treg (x, xt) = env.!["x"] in
    let S.Timm (y, yt) = env.!["y"] in
    let S.Tlbl yes = env.!["yes"] in
    let S.Tlbl no = env.!["no"] in
    let y = Bv.to_int64 y in
    let cc = if neg then Ce else Cne in
    let@ oy = with_imm xt y yt in [
      I.test (Oreg (x, xt)) oy;
      I.jcc cc yes;
      I.jmp (Jlbl no)
    ]
  ]

  let jcc_rsym_test_x_y ?(neg = false) env = [%rule
    let S.Treg (x, xt) = env.!["x"] in
    let S.Tsym (y, yo) = env.!["y"] in
    let S.Tlbl yes = env.!["yes"] in
    let S.Tlbl no = env.!["no"] in
    let* tmp = fresh_reg in
    let cc = if neg then Ce else Cne in [
      lea_sym tmp y yo;
      I.test (Oreg (x, xt)) (Oreg (tmp, `i64));
      I.jcc cc yes;
      I.jmp (Jlbl no)
    ]
  ]

  let jcc_rr_cmp cmp cc env = [%rule
    let S.Treg (x, xt) = env.!["x"] in
    let S.Treg (y, yt) = env.!["y"] in
    let S.Tlbl yes = env.!["yes"] in
    let S.Tlbl no = env.!["no"] in [
      cmp (Oreg (x, xt)) (Oreg (y, yt));
      I.jcc cc yes;
      I.jmp (Jlbl no)
    ]
  ]
  [@@specialise]

  let jcc_rr_x_y     = jcc_rr_cmp I.cmp
  let jcc_rr_f32_x_y = jcc_rr_cmp I.ucomiss
  let jcc_rr_f64_x_y = jcc_rr_cmp I.ucomisd

  let jcc_rf32_x_y cc env = [%rule
    let S.Treg (x, xt) = env.!["x"] in
    let S.Tf32 y = env.!["y"] in
    let S.Tlbl yes = env.!["yes"] in
    let S.Tlbl no = env.!["no"] in
    guard (Type.equal_basic xt `f32);
    let* l, addr = fresh_label_addr in [
      I.ucomiss (Oreg (x, xt)) (Omem (addr, `f32));
      I.jcc cc yes;
      I.jmp (Jlbl no);
      I.fp32 l y
    ]
  ]

  let jcc_fr32_x_y cc env = [%rule
    let S.Tf32 x = env.!["x"] in
    let S.Treg (y, yt) = env.!["y"] in
    let S.Tlbl yes = env.!["yes"] in
    let S.Tlbl no = env.!["no"] in
    guard (Type.equal_basic yt `f32);
    let* l, addr = fresh_label_addr in [
      I.ucomiss (Oreg (y, yt)) (Omem (addr, `f32));
      I.jcc (flip_cc cc) yes;
      I.jmp (Jlbl no);
      I.fp32 l x
    ]
  ]

  let jcc_rf64_x_y cc env = [%rule
    let S.Treg (x, xt) = env.!["x"] in
    let S.Tf64 y = env.!["y"] in
    let S.Tlbl yes = env.!["yes"] in
    let S.Tlbl no = env.!["no"] in
    guard (Type.equal_basic xt `f64);
    let* l, addr = fresh_label_addr in [
      I.ucomisd (Oreg (x, xt)) (Omem (addr, `f64));
      I.jcc cc yes;
      I.jmp (Jlbl no);
      I.fp64 l y
    ]
  ]

  let jcc_fr64_x_y cc env = [%rule
    let S.Tf64 x = env.!["x"] in
    let S.Treg (y, yt) = env.!["y"] in
    let S.Tlbl yes = env.!["yes"] in
    let S.Tlbl no = env.!["no"] in
    guard (Type.equal_basic yt `f64);
    let* l, addr = fresh_label_addr in [
      I.ucomisd (Oreg (y, yt)) (Omem (addr, `f64));
      I.jcc (flip_cc cc) yes;
      I.jmp (Jlbl no);
      I.fp64 l x
    ]
  ]

  let jcc_ri_x_y cc env = [%rule
    let S.Treg (x, xt) = env.!["x"] in
    let S.Timm (y, yt) = env.!["y"] in
    let S.Tlbl yes = env.!["yes"] in
    let S.Tlbl no = env.!["no"] in
    let y = Bv.to_int64 y in
    let@ oy = with_imm xt y yt in [
      I.cmp (Oreg (x, xt)) oy;
      I.jcc cc yes;
      I.jmp (Jlbl no)
    ]
  ]

  let jcc_rsym_x_y cc env = [%rule
    let S.Treg (x, xt) = env.!["x"] in
    let S.Tsym (y, yo) = env.!["y"] in
    let S.Tlbl yes = env.!["yes"] in
    let S.Tlbl no = env.!["no"] in
    let* tmp = fresh_reg in [
      lea_sym tmp y yo;
      I.cmp (Oreg (x, xt)) (Oreg (tmp, `i64));
      I.jcc cc yes;
      I.jmp (Jlbl no)
    ]
  ]

  let jcc_symi_x_y cc env = [%rule
    let S.Tsym (x, xo) = env.!["x"] in
    let S.Timm (y, yt) = env.!["y"] in
    guard (Type.equal_imm yt `i64);
    let S.Tlbl yes = env.!["yes"] in
    let S.Tlbl no = env.!["no"] in
    let* tmp = fresh_reg in
    let y = Bv.to_int64 y in [
      lea_sym tmp x xo;
      I.cmp (Oreg (tmp, `i64)) (Oimm (y, yt));
      I.jcc cc yes;
      I.jmp (Jlbl no)
    ]
  ]

  let jcc_symsym_x_y cc env = [%rule
    let S.Tsym (x, xo) = env.!["x"] in
    let S.Tsym (y, yo) = env.!["y"] in
    let S.Tlbl yes = env.!["yes"] in
    let S.Tlbl no = env.!["no"] in
    let* tmp1 = fresh_reg in
    let* tmp2 = fresh_reg in [
      lea_sym tmp1 x xo;
      lea_sym tmp2 y yo;
      I.cmp (Oreg (tmp1, `i64)) (Oreg (tmp2, `i64));
      I.jcc cc yes;
      I.jmp (Jlbl no)
    ]
  ]

  (* `br (x & y !=/== 0) yes no` via `test`, dispatching on the form of `y`. *)
  let br_test ?(neg = false) () env = [%rule
    match env.!["y"] with
    | S.Treg _ -> continue (jcc_rr_test_x_y ~neg env)
    | S.Timm _ -> continue (jcc_ri_test_x_y ~neg env)
    | S.Tsym _ -> continue (jcc_rsym_test_x_y ~neg env)
    | _ -> fail
  ]

  (* `br (x <cmp> y) yes no` at integer widths, dispatching on the operand
     forms. *)
  let br_icmp cc env = [%rule
    match env.!["x"], env.!["y"] with
    | S.Treg _, S.Treg _ -> continue (jcc_rr_x_y cc env)
    | S.Treg _, S.Timm _ -> continue (jcc_ri_x_y cc env)
    | S.Treg _, S.Tsym _ -> continue (jcc_rsym_x_y cc env)
    | S.Tsym _, S.Timm _ -> continue (jcc_symi_x_y cc env)
    | S.Tsym _, S.Tsym _ -> continue (jcc_symsym_x_y cc env)
    | _ -> fail
  ]

  (* `br (x <fcmp> y) yes no` at f32, dispatching on the operand forms. *)
  let br_fcmp32 cc env = [%rule
    match env.!["x"], env.!["y"] with
    | S.Treg _, S.Treg _ -> continue (jcc_rr_f32_x_y cc env)
    | S.Treg _, S.Tf32 _ -> continue (jcc_rf32_x_y cc env)
    | S.Tf32 _, S.Treg _ -> continue (jcc_fr32_x_y cc env)
    | _ -> fail
  ]

  (* `br (x <fcmp> y) yes no` at f64, dispatching on the operand forms. *)
  let br_fcmp64 cc env = [%rule
    match env.!["x"], env.!["y"] with
    | S.Treg _, S.Treg _ -> continue (jcc_rr_f64_x_y cc env)
    | S.Treg _, S.Tf64 _ -> continue (jcc_rf64_x_y cc env)
    | S.Tf64 _, S.Treg _ -> continue (jcc_fr64_x_y cc env)
    | _ -> fail
  ]

  (* Default to 8-bit *)
  let setcc_r_zero_x_y ?(neg = false) env = [%rule
    let S.Treg (x, _) = env.!["x"] in
    let S.Treg (y, yt) = env.!["y"] in
    let cc = if neg then Cne else Ce in [
      I.xor (Oreg (x, `i32)) (Oreg (x, `i32));
      I.test (Oreg (y, yt)) (Oreg (y, yt));
      I.setcc cc (Oreg (x, `i8))
    ]
  ]

  (* Default to 8-bit *)
  let setcc_r_less_than_zero_x_y ?(neg = false) env = [%rule
    let S.Treg (x, _) = env.!["x"] in
    let S.Treg (y, yt) = env.!["y"] in
    let cc = if neg then Cns else Cs in [
      I.xor (Oreg (x, `i32)) (Oreg (x, `i32));
      I.test (Oreg (y, yt)) (Oreg (y, yt));
      I.setcc cc (Oreg (x, `i8))
    ]
  ]

  (* Default to 8-bit *)
  (* `x = (y & z) <cmp> 0` via `test`, dispatching on the form of `z`. All arms
     zero `x` first because `setcc` writes only the low byte, so we avoid a false
     dependency. *)
  let setcc_test ?(neg = false) () env = [%rule
    let S.Treg (x, _) = env.!["x"] in
    let S.Treg (y, yt) = env.!["y"] in
    let cc = if neg then Ce else Cne in
    match env.!["z"] with
    | S.Treg (z, zt) -> [
        I.xor (Oreg (x, `i32)) (Oreg (x, `i32));
        I.test (Oreg (y, yt)) (Oreg (z, zt));
        I.setcc cc (Oreg (x, `i8))
      ]
    | S.Timm (z, zt) ->
      let z = Bv.to_int64 z in
      let@ oz = with_imm yt z zt in [
        I.xor (Oreg (x, `i32)) (Oreg (x, `i32));
        I.test (Oreg (y, yt)) oz;
        I.setcc cc (Oreg (x, `i8))
      ]
    | S.Tsym (z, zo) ->
      let* tmp = fresh_reg in [
        I.xor (Oreg (x, `i32)) (Oreg (x, `i32));
        lea_sym tmp z zo;
        I.test (Oreg (y, yt)) (Oreg (tmp, `i64));
        I.setcc cc (Oreg (x, `i8))
      ]
    | _ -> fail
  ]

  (* `x = y <cmp> z` at integer widths (result via `setcc cc`), dispatching on
     the operand forms. All arms zero `x` first because `setcc` writes only the
     low byte, so the upper bytes would otherwise be garbage when the flag is
     later widened to a full register (and we would have a false dependency
     on the unused upper bits). Defaults to 8-bit. *)
  let setcc cc env = [%rule
    let S.Treg (x, _) = env.!["x"] in
    match env.!["y"], env.!["z"] with
    | S.Treg (y, yt), S.Treg (z, zt) -> [
        I.xor (Oreg (x, `i32)) (Oreg (x, `i32));
        I.cmp (Oreg (y, yt)) (Oreg (z, zt));
        I.setcc cc (Oreg (x, `i8))
      ]
    | S.Treg (y, yt), S.Timm (z, zt) ->
      let z = Bv.to_int64 z in
      let@ oz = with_imm yt z zt in [
        I.xor (Oreg (x, `i32)) (Oreg (x, `i32));
        I.cmp (Oreg (y, yt)) oz;
        I.setcc cc (Oreg (x, `i8))
      ]
    | S.Timm (y, yt), S.Treg (z, zt) ->
      let y = Bv.to_int64 y in
      let@ oy = with_imm zt y yt in [
        I.xor (Oreg (x, `i32)) (Oreg (x, `i32));
        I.cmp (Oreg (z, zt)) oy;
        I.setcc (swap_cc cc) (Oreg (x, `i8))
      ]
    | S.Treg (y, yt), S.Tsym (z, zo) ->
      let* tmp = fresh_reg in [
        I.xor (Oreg (x, `i32)) (Oreg (x, `i32));
        lea_sym tmp z zo;
        I.cmp (Oreg (y, yt)) (Oreg (tmp, `i64));
        I.setcc cc (Oreg (x, `i8))
      ]
    | S.Tsym (y, yo), S.Timm (z, zt) ->
      guard (Type.equal_imm zt `i64);
      let* tmp = fresh_reg in
      let z = Bv.to_int64 z in [
        I.xor (Oreg (x, `i32)) (Oreg (x, `i32));
        lea_sym tmp y yo;
        I.cmp (Oreg (tmp, `i64)) (Oimm (z, zt));
        I.setcc cc (Oreg (x, `i8))
      ]
    | S.Tsym (y, yo), S.Tsym (z, zo) ->
      let* tmp1 = fresh_reg in
      let* tmp2 = fresh_reg in [
        I.xor (Oreg (x, `i32)) (Oreg (x, `i32));
        lea_sym tmp1 y yo;
        lea_sym tmp2 z zo;
        I.cmp (Oreg (tmp1, `i64)) (Oreg (tmp2, `i64));
        I.setcc cc (Oreg (x, `i8))
      ]
    | _ -> fail
  ]

  (* `x = y <fcmp> z` at f32 (result via `setcc cc`), dispatching on the
     operand forms. The const-reg form swaps operands and flips the condition. *)
  let setcc_f32 cc env = [%rule
    let S.Treg (x, _) = env.!["x"] in
    match env.!["y"], env.!["z"] with
    | S.Treg (y, yt), S.Treg (z, zt) -> [
        I.xor (Oreg (x, `i32)) (Oreg (x, `i32));
        I.ucomiss (Oreg (y, yt)) (Oreg (z, zt));
        I.setcc cc (Oreg (x, `i8))
      ]
    | S.Treg (y, yt), S.Tf32 z ->
      guard (Type.equal_basic yt `f32);
      let* l, addr = fresh_label_addr in [
        I.xor    (Oreg (x, `i32)) (Oreg (x, `i32));
        I.ucomiss (Oreg (y, yt)) (Omem (addr, `f32));
        I.setcc cc (Oreg (x, `i8));
        I.fp32 l z
      ]
    | S.Tf32 y, S.Treg (z, zt) ->
      guard (Type.equal_basic zt `f32);
      let* l, addr = fresh_label_addr in [
        I.xor (Oreg (x, `i32)) (Oreg (x, `i32));
        I.ucomiss (Oreg (z, zt)) (Omem (addr, `f32));
        I.setcc (flip_cc cc) (Oreg (x, `i8));
        I.fp32 l y
      ]
    | _ -> fail
  ]

  (* `x = y <fcmp> z` at f64, dispatching on the operand forms. *)
  let setcc_f64 cc env = [%rule
    let S.Treg (x, _) = env.!["x"] in
    match env.!["y"], env.!["z"] with
    | S.Treg (y, yt), S.Treg (z, zt) -> [
        I.xor (Oreg (x, `i32)) (Oreg (x, `i32));
        I.ucomisd (Oreg (y, yt)) (Oreg (z, zt));
        I.setcc cc (Oreg (x, `i8))
      ]
    | S.Treg (y, yt), S.Tf64 z ->
      guard (Type.equal_basic yt `f64);
      let* l, addr = fresh_label_addr in [
        I.xor    (Oreg (x, `i32)) (Oreg (x, `i32));
        I.ucomisd (Oreg (y, yt)) (Omem (addr, `f64));
        I.setcc cc (Oreg (x, `i8));
        I.fp64 l z
      ]
    | S.Tf64 y, S.Treg (z, zt) ->
      guard (Type.equal_basic zt `f64);
      let* l, addr = fresh_label_addr in [
        I.xor (Oreg (x, `i32)) (Oreg (x, `i32));
        I.ucomisd (Oreg (z, zt)) (Omem (addr, `f64));
        I.setcc (flip_cc cc) (Oreg (x, `i8));
        I.fp64 l y
      ]
    | _ -> fail
  ]

  (* 8-bit cmov is not supported, but we can just use
     the 32-bit variant and pretend that nothing happened.

     If the input program is well-typed then this should
     be kosher.
  *)
  let sel_i8_ty = function
    | `i8 -> `i32
    | t -> t

  let sel_yn_rr cc x xt pre cmp env = [%rule
    let xt' = sel_i8_ty xt in
    let S.Treg (yes, yes_t) = env.!["yes"] in
    let S.Treg (no, no_t) = env.!["no"] in
    guard (Type.equal_basic xt yes_t);
    guard (Type.equal_basic xt no_t);
    pre @ [
      I.mov (Oreg (x, xt')) (Oreg (no, xt'));
      cmp;
      I.cmov cc (Oreg (x, xt')) (Oreg (yes, xt'));
    ]
  ]

  let sel_yn_ri cc x xt pre cmp env = [%rule
    let xt' = sel_i8_ty xt in
    let S.Treg (yes, yes_t) = env.!["yes"] in
    let S.Timm (no, no_t) = env.!["no"] in
    guard (Type.equal_basic xt yes_t);
    guard (Type.equal_basic xt (bty no_t));
    pre @ [
      I.mov (Oreg (x, xt')) (Oimm (Bv.to_int64 no, no_t));
      cmp;
      I.cmov cc (Oreg (x, xt')) (Oreg (yes, xt'));
    ]
  ]

  let sel_yn_ir cc x xt pre cmp env = [%rule
    let xt' = sel_i8_ty xt in
    let S.Timm (yes, yes_t) = env.!["yes"] in
    let S.Treg (no, no_t) = env.!["no"] in
    guard (Type.equal_basic xt (bty yes_t));
    guard (Type.equal_basic xt no_t);
    pre @ [
      I.mov (Oreg (x, xt')) (Oimm (Bv.to_int64 yes, yes_t));
      cmp;
      I.cmov (negate_cc cc) (Oreg (x, xt')) (Oreg (no, xt'));
    ]
  ]

  let sel_yn_ii cc x xt pre cmp env = [%rule
    let xt' = sel_i8_ty xt in
    let S.Timm (yes, yes_t) = env.!["yes"] in
    let S.Timm (no, no_t) = env.!["no"] in
    guard (Type.equal_basic xt (bty yes_t));
    guard (Type.equal_basic xt (bty no_t));
    let* tmp_yes = fresh_reg in
    pre @ [
      I.mov (Oreg (tmp_yes, xt')) (Oimm (Bv.to_int64 yes, yes_t));
      I.mov (Oreg (x, xt')) (Oimm (Bv.to_int64 no, no_t));
      cmp;
      I.cmov cc (Oreg (x, xt')) (Oreg (tmp_yes, xt'));
    ]
  ]

  let sel_rr_x_y_z yn cc env = [%rule
    let S.Treg (x, xt) = env.!["x"] in
    let S.Treg (y, yt) = env.!["y"] in
    let S.Treg (z, zt) = env.!["z"] in
    continue (yn cc x xt [] (I.cmp (Oreg (y, yt)) (Oreg (z, zt))) env)
  ] [@@specialise]

  let sel_ri_x_y_z yn cc env = [%rule
    let S.Treg (x, xt) = env.!["x"] in
    let S.Treg (y, yt) = env.!["y"] in
    let S.Timm (z, zt) = env.!["z"] in
    let z = Bv.to_int64 z in
    continue (
      if fits_imm yt z then
        yn cc x xt [] (I.cmp (Oreg (y, yt)) (Oimm (z, zt))) env
      else
        let* tmp = C.Var.fresh >>| Rv.var in
        yn cc x xt
          [I.mov (Oreg (tmp, bty zt)) (Oimm (z, zt))]
          (I.cmp (Oreg (y, yt)) (Oreg (tmp, bty zt)))
          env)
  ] [@@specialise]

  (* Condition compares a register against a symbol's address. *)
  let sel_rsym_x_y_z yn cc env = [%rule
    let S.Treg (x, xt) = env.!["x"] in
    let S.Treg (y, yt) = env.!["y"] in
    let S.Tsym (s, o) = env.!["z"] in
    continue (
      let* tmp = C.Var.fresh >>| Rv.var in
      yn cc x xt
        [lea_sym tmp s o]
        (I.cmp (Oreg (y, yt)) (Oreg (tmp, `i64)))
        env)
  ] [@@specialise]

  let sel_zero_x_y yn ?(neg = false) ?(eq = true) env = [%rule
    let S.Treg (x, xt) = env.!["x"] in
    let S.Treg (y, yt) = env.!["y"] in
    let cc = if eq
      then (if neg then Cne else Ce)
      else (if neg then Cns else Cs) in
    continue (yn cc x xt [] (I.test (Oreg (y, yt)) (Oreg (y, yt))) env)
  ]

  (* Pick the yes/no-value handler from the forms of `yes` and `no` (each is
     always a register or an immediate). *)
  let sel_yn env = match env.!["yes"], env.!["no"] with
    | S.Treg _, S.Treg _ -> Some sel_yn_rr
    | S.Treg _, S.Timm _ -> Some sel_yn_ri
    | S.Timm _, S.Treg _ -> Some sel_yn_ir
    | S.Timm _, S.Timm _ -> Some sel_yn_ii
    | _ -> None

  (* `x = sel (y <cmp> z) yes no` at integer widths: pick the yes/no handler,
     then dispatch on the comparison operand forms. *)
  let sel_cmov cc env = [%rule
    let*! yn = sel_yn env in
    match env.!["y"], env.!["z"] with
    | S.Treg _, S.Treg _ -> continue (sel_rr_x_y_z yn cc env)
    | S.Treg _, S.Timm _ -> continue (sel_ri_x_y_z yn cc env)
    | S.Treg _, S.Tsym _ -> continue (sel_rsym_x_y_z yn cc env)
    | _ -> fail
  ]

  (* `x = sel (y <cmp> 0) yes no`: pick the yes/no handler, compare against
     zero via `test`. *)
  let sel_zero ?(neg = false) ?(eq = true) () env = [%rule
    let*! yn = sel_yn env in
    continue (sel_zero_x_y yn ~neg ~eq env)
  ]

  let sel_fcmp_rr ucomi yn cc env = [%rule
    let S.Treg (x, xt) = env.!["x"] in
    let S.Treg (y, yt) = env.!["y"] in
    let S.Treg (z, zt) = env.!["z"] in
    continue (yn cc x xt [] (ucomi (Oreg (y, yt)) (Oreg (z, zt))) env)
  ]

  let sel_fcmp_rf32 yn cc env = [%rule
    let S.Treg (x, xt) = env.!["x"] in
    let S.Treg (y, yt) = env.!["y"] in
    let S.Tf32 z = env.!["z"] in
    guard (Type.equal_basic yt `f32);
    continue (
      let* l, addr = fresh_label_addr in
      yn cc x xt [I.fp32 l z] (I.ucomiss (Oreg (y, yt)) (Omem (addr, `f32))) env)
  ]

  let sel_fcmp_rf64 yn cc env = [%rule
    let S.Treg (x, xt) = env.!["x"] in
    let S.Treg (y, yt) = env.!["y"] in
    let S.Tf64 z = env.!["z"] in
    guard (Type.equal_basic yt `f64);
    continue (
      let* l, addr = fresh_label_addr in
      yn cc x xt [I.fp64 l z] (I.ucomisd (Oreg (y, yt)) (Omem (addr, `f64))) env)
  ]

  let sel_fcmp_fr32 yn cc env = [%rule
    let S.Treg (x, xt) = env.!["x"] in
    let S.Tf32 y = env.!["y"] in
    let S.Treg (z, zt) = env.!["z"] in
    guard (Type.equal_basic zt `f32);
    continue (
      let* l, addr = fresh_label_addr in
      yn (flip_cc cc) x xt [I.fp32 l y] (I.ucomiss (Oreg (z, zt)) (Omem (addr, `f32))) env)
  ]

  let sel_fcmp_fr64 yn cc env = [%rule
    let S.Treg (x, xt) = env.!["x"] in
    let S.Tf64 y = env.!["y"] in
    let S.Treg (z, zt) = env.!["z"] in
    guard (Type.equal_basic zt `f64);
    continue (
      let* l, addr = fresh_label_addr in
      yn (flip_cc cc) x xt [I.fp64 l y] (I.ucomisd (Oreg (z, zt)) (Omem (addr, `f64))) env)
  ]

  (* `x = sel (y <fcmp> z) yes no` producing an integer result via cmov. Pick
     the yes/no handler, then dispatch on the fp comparison operand forms. *)
  let sel_fcmp32 cc env = [%rule
    let*! yn = sel_yn env in
    match env.!["y"], env.!["z"] with
    | S.Treg _, S.Treg _ -> continue (sel_fcmp_rr I.ucomiss yn cc env)
    | S.Treg _, S.Tf32 _ -> continue (sel_fcmp_rf32 yn cc env)
    | S.Tf32 _, S.Treg _ -> continue (sel_fcmp_fr32 yn cc env)
    | _ -> fail
  ]

  let sel_fcmp64 cc env = [%rule
    let*! yn = sel_yn env in
    match env.!["y"], env.!["z"] with
    | S.Treg _, S.Treg _ -> continue (sel_fcmp_rr I.ucomisd yn cc env)
    | S.Treg _, S.Tf64 _ -> continue (sel_fcmp_rf64 yn cc env)
    | S.Tf64 _, S.Treg _ -> continue (sel_fcmp_fr64 yn cc env)
    | _ -> fail
  ]

  let f32_reg rv f = f (Oreg (rv, `f32), [])
  let f64_reg rv f = f (Oreg (rv, `f64), [])

  let f32_const fv f =
    let* l, a = fresh_label_addr in
    f (Omem (a, `f32), [I.fp32 l fv])

  let f32v_const fv f =
    let* l, a = fresh_label_addr in
    f (Omem (a, `v128), [I.fp32v l fv])

  let f64_const fv f =
    let* l, a = fresh_label_addr in
    f (Omem (a, `f64), [I.fp64 l fv])

  let f64v_const fv f =
    let* l, a = fresh_label_addr in
    f (Omem (a, `v128), [I.fp64v l fv])

  let sel_fcore32 p x with_y with_z with_yes with_no =
    let* tmp = C.Var.fresh >>| Rv.var in
    let@ y_op, y_ps = with_y in
    let@ z_op, z_ps = with_z in
    let@ yes_op, yes_ps = with_yes in
    let@ no_op, no_ps = with_no in [
      I.movss (Oreg (tmp, `f32)) y_op;
      I.cmpss p (Oreg (tmp, `f32)) z_op;
      I.movss (Oreg (x, `f32)) yes_op;
      I.andps (Oreg (x, `f32)) (Oreg (tmp, `f32));
      I.andnps (Oreg (tmp, `f32)) no_op;
      I.orps (Oreg (x, `f32)) (Oreg (tmp, `f32));
    ] @!! (y_ps @ z_ps @ yes_ps @ no_ps)

  let sel_fcore64 p x with_y with_z with_yes with_no =
    let* tmp = C.Var.fresh >>| Rv.var in
    let@ y_op, y_ps = with_y in
    let@ z_op, z_ps = with_z in
    let@ yes_op, yes_ps = with_yes in
    let@ no_op, no_ps = with_no in [
      I.movsd (Oreg (tmp, `f64)) y_op;
      I.cmpsd p (Oreg (tmp, `f64)) z_op;
      I.movsd (Oreg (x, `f64)) yes_op;
      I.andpd (Oreg (x, `f64)) (Oreg (tmp, `f64));
      I.andnpd (Oreg (tmp, `f64)) no_op;
      I.orpd (Oreg (x, `f64)) (Oreg (tmp, `f64));
    ] @!! (y_ps @ z_ps @ yes_ps @ no_ps)

  let regvar_or_f32 env v fl fr = match env.![v] with
    | S.Treg (r, _) -> Some (fl r)
    | S.Tf32 s -> Some (fr s)
    | _ -> None

  let regvar_or_f64 env v fl fr = match env.![v] with
    | S.Treg (r, _) -> Some (fl r)
    | S.Tf64 d -> Some (fr d)
    | _ -> None

  let sel_f32_x_y_z p env = [%rule
    let S.Treg (x, _) = env.!["x"] in
    let Some with_y = regvar_or_f32 env "y" f32_reg f32_const in
    let Some with_z = regvar_or_f32 env "z" f32_reg f32_const in
    let Some with_yes = regvar_or_f32 env "yes" f32_reg f32_const in
    let Some with_no = regvar_or_f32 env "no" f32_reg f32v_const in
    continue (sel_fcore32 p x with_y with_z with_yes with_no)
  ] [@@specialise]

  let sel_f64_x_y_z p env = [%rule
    let S.Treg (x, _) = env.!["x"] in
    let Some with_y = regvar_or_f64 env "y" f64_reg f64_const in
    let Some with_z = regvar_or_f64 env "z" f64_reg f64_const in
    let Some with_yes = regvar_or_f64 env "yes" f64_reg f64_const in
    let Some with_no = regvar_or_f64 env "no" f64_reg f64v_const in
    continue (sel_fcore64 p x with_y with_z with_yes with_no)
  ] [@@specialise]

  let load_add_mul_rr_scale_imm_x_y_z_w s env = [%rule
    let S.Treg (x, xt) = env.!["x"] in
    let S.Treg (y, _) = env.!["y"] in
    let S.Treg (z, _) = env.!["z"] in
    let S.Timm (w, _) = env.!["w"] in
    let w = Bv.to_int64 w in
    guard (fits_int32_pos w);
    let w = Int64.to_int32_trunc w in
    let addr = Omem (Abisd (y, z, s, w), mty xt) in
    [load_typed xt x addr]
  ]

  let load_add_mul_rr_scale_neg_imm_x_y_z_w s env = [%rule
    let S.Treg (x, xt) = env.!["x"] in
    let S.Treg (y, _) = env.!["y"] in
    let S.Treg (z, _) = env.!["z"] in
    let S.Timm (w, _) = env.!["w"] in
    let w = Bv.to_int64 w in
    let nw = Int64.neg w in
    guard (fits_int32_neg nw);
    let w = Int64.to_int32_trunc nw in
    let addr = Omem (Abisd (y, z, s, w), mty xt) in
    [load_typed xt x addr]
  ]

  let load_add_mul_rr_scale_x_y_z s env = [%rule
    let S.Treg (x, xt) = env.!["x"] in
    let S.Treg (y, _) = env.!["y"] in
    let S.Treg (z, _) = env.!["z"] in
    let addr = Omem (Abis (y, z, s), mty xt) in
    [load_typed xt x addr]
  ]

  (* `x = load y`, dispatching on the address form. *)
  let load_basic env = [%rule
    let S.Treg (x, xt) = env.!["x"] in
    match env.!["y"] with
    | S.Treg (y, _) -> [load_typed xt x (Omem (Ab y, mty xt))]
    | S.Tsym (s, o) ->
      guard (sym_disp_fits o);
      [load_typed xt x (Omem (Asym (s, o), mty xt))]
    | _ -> fail
  ]

  (* `x = load (y + z)`, dispatching on the form of the offset `z`. *)
  let load_add env = [%rule
    let S.Treg (x, xt) = env.!["x"] in
    let S.Treg (y, _) = env.!["y"] in
    match env.!["z"] with
    | S.Timm (z, _) ->
      let z = Bv.to_int64 z in
      guard (fits_sext32 z);
      let z = Int64.to_int32_trunc z in
      [load_typed xt x (Omem (Abd (y, z), mty xt))]
    | S.Treg (z, _) ->
      [load_typed xt x (Omem (Abis (y, z, S1), mty xt))]
    | _ -> fail
  ]

  (* `x = sext (load y)` from `zt`, dispatching on the address form. *)
  let load_sext zt env = [%rule
    let S.Treg (x, xt) = env.!["x"] in
    match env.!["y"] with
    | S.Treg (y, _) -> [sext_load_typed xt zt x (Omem (Ab y, mty zt))]
    | S.Tsym (s, o) ->
      guard (sym_disp_fits o);
      [sext_load_typed xt zt x (Omem (Asym (s, o), mty zt))]
    | _ -> fail
  ]

  (* `x = zext (load y)` from `zt`, dispatching on the address form. *)
  let load_zext zt env = [%rule
    let S.Treg (x, _) = env.!["x"] in
    match env.!["y"] with
    | S.Treg (y, _) -> [zext_load_typed zt x (Omem (Ab y, mty zt))]
    | S.Tsym (s, o) ->
      guard (sym_disp_fits o);
      [zext_load_typed zt x (Omem (Asym (s, o), mty zt))]
    | _ -> fail
  ]

  (* `x = sext (load (y + z))` from `zt`, dispatching on the offset form. *)
  let load_sext_add zt env = [%rule
    let S.Treg (x, xt) = env.!["x"] in
    let S.Treg (y, _) = env.!["y"] in
    match env.!["z"] with
    | S.Timm (z, _) ->
      let z = Bv.to_int64 z in
      guard (fits_sext32 z);
      let z = Int64.to_int32_trunc z in
      [sext_load_typed xt zt x (Omem (Abd (y, z), mty zt))]
    | S.Treg (z, _) ->
      [sext_load_typed xt zt x (Omem (Abis (y, z, S1), mty zt))]
    | _ -> fail
  ]

  (* `x = zext (load (y + z))` from `zt`, dispatching on the offset form. *)
  let load_zext_add zt env = [%rule
    let S.Treg (x, _) = env.!["x"] in
    let S.Treg (y, _) = env.!["y"] in
    match env.!["z"] with
    | S.Timm (z, _) ->
      let z = Bv.to_int64 z in
      guard (fits_sext32 z);
      let z = Int64.to_int32_trunc z in
      [zext_load_typed zt x (Omem (Abd (y, z), mty zt))]
    | S.Treg (z, _) ->
      [zext_load_typed zt x (Omem (Abis (y, z, S1), mty zt))]
    | _ -> fail
  ]

  let load_sext_add_mul_rr_scale_x_y_z zt s env = [%rule
    let S.Treg (x, xt) = env.!["x"] in
    let S.Treg (y, _) = env.!["y"] in
    let S.Treg (z, _) = env.!["z"] in
    let addr = Omem (Abis (y, z, s), mty zt) in
    [sext_load_typed xt zt x addr]
  ]

  let load_zext_add_mul_rr_scale_x_y_z zt s env = [%rule
    let S.Treg (x, _) = env.!["x"] in
    let S.Treg (y, _) = env.!["y"] in
    let S.Treg (z, _) = env.!["z"] in
    let addr = Omem (Abis (y, z, s), mty zt) in
    [zext_load_typed zt x addr]
  ]

  let load_sext_add_mul_rr_scale_imm_x_y_z_w zt s env = [%rule
    let S.Treg (x, xt) = env.!["x"] in
    let S.Treg (y, _) = env.!["y"] in
    let S.Treg (z, _) = env.!["z"] in
    let S.Timm (w, _) = env.!["w"] in
    let w = Bv.to_int64 w in
    guard (fits_int32_pos w);
    let w = Int64.to_int32_trunc w in
    let addr = Omem (Abisd (y, z, s, w), mty zt) in
    [sext_load_typed xt zt x addr]
  ]

  let load_zext_add_mul_rr_scale_imm_x_y_z_w zt s env = [%rule
    let S.Treg (x, _) = env.!["x"] in
    let S.Treg (y, _) = env.!["y"] in
    let S.Treg (z, _) = env.!["z"] in
    let S.Timm (w, _) = env.!["w"] in
    let w = Bv.to_int64 w in
    guard (fits_int32_pos w);
    let w = Int64.to_int32_trunc w in
    let addr = Omem (Abisd (y, z, s, w), mty zt) in
    [zext_load_typed zt x addr]
  ]

  let load_sext_add_mul_rr_scale_neg_imm_x_y_z_w zt s env = [%rule
    let S.Treg (x, xt) = env.!["x"] in
    let S.Treg (y, _) = env.!["y"] in
    let S.Treg (z, _) = env.!["z"] in
    let S.Timm (w, _) = env.!["w"] in
    let w = Bv.to_int64 w in
    let nw = Int64.neg w in
    guard (fits_int32_neg nw);
    let w = Int64.to_int32_trunc nw in
    let addr = Omem (Abisd (y, z, s, w), mty zt) in
    [sext_load_typed xt zt x addr]
  ]

  let load_zext_add_mul_rr_scale_neg_imm_x_y_z_w zt s env = [%rule
    let S.Treg (x, _) = env.!["x"] in
    let S.Treg (y, _) = env.!["y"] in
    let S.Treg (z, _) = env.!["z"] in
    let S.Timm (w, _) = env.!["w"] in
    let w = Bv.to_int64 w in
    let nw = Int64.neg w in
    guard (fits_int32_neg nw);
    let w = Int64.to_int32_trunc nw in
    let addr = Omem (Abisd (y, z, s, w), mty zt) in
    [zext_load_typed zt x addr]
  ]

  let store_rr_x_y env = [%rule
    let S.Treg (x, xt) = env.!["x"] in
    let S.Treg (y, _) = env.!["y"] in
    let addr = Omem (Ab y, mty xt) in
    [mov_typed xt addr (Oreg (x, xt))]
  ]

  let store_ri_x_y env = [%rule
    let S.Timm (x, xt) = env.!["x"] in
    let S.Treg (y, _) = env.!["y"] in
    let@ o = with_imm xt (Bv.to_int64 x) xt in
    [I.mov (Omem (Ab y, mty xt)) o]
  ]

  let store_rf32_x_y env = [%rule
    let S.Tf32 x = env.!["x"] in
    let S.Treg (y, _) = env.!["y"] in
    let* l, addr = fresh_label_addr in [
      I.movss (Omem (Ab y, mty `f32)) (Omem (addr, `f32));
      I.fp32 l x
    ]
  ]

  let store_rf64_x_y env = [%rule
    let S.Tf64 x = env.!["x"] in
    let S.Treg (y, _) = env.!["y"] in
    let* l, addr = fresh_label_addr in [
      I.movsd (Omem (Ab y, mty `f64)) (Omem (addr, `f64));
      I.fp64 l x
    ]
  ]

  let store_add_mul_rr_scale_imm_x_y_z_w s env = [%rule
    let S.Treg (x, xt) = env.!["x"] in
    let S.Treg (y, _) = env.!["y"] in
    let S.Treg (z, _) = env.!["z"] in
    let S.Timm (w, _) = env.!["w"] in
    let w = Bv.to_int64 w in
    guard (fits_int32_pos w);
    let w = Int64.to_int32_trunc w in
    let addr = Omem (Abisd (y, z, s, w), mty xt) in
    [mov_typed xt addr (Oreg (x, xt))]
  ]

  let store_add_mul_rr_scale_neg_imm_x_y_z_w s env = [%rule
    let S.Treg (x, xt) = env.!["x"] in
    let S.Treg (y, _) = env.!["y"] in
    let S.Treg (z, _) = env.!["z"] in
    let S.Timm (w, _) = env.!["w"] in
    let w = Bv.to_int64 w in
    let nw = Int64.neg w in
    guard (fits_int32_neg nw);
    let w = Int64.to_int32_trunc nw in
    let addr = Omem (Abisd (y, z, s, w), mty xt) in
    [mov_typed xt addr (Oreg (x, xt))]
  ]

  let store_add_mul_rr_scale_x_y_z s env = [%rule
    let S.Treg (x, xt) = env.!["x"] in
    let S.Treg (y, _) = env.!["y"] in
    let S.Treg (z, _) = env.!["z"] in
    let addr = Omem (Abis (y, z, s), mty xt) in
    [mov_typed xt addr (Oreg (x, xt))]
  ]

  let store_rri_add_x_y_z env = [%rule
    let S.Treg (x, xt) = env.!["x"] in
    let S.Treg (y, _) = env.!["y"] in
    let S.Timm (z, _) = env.!["z"] in
    let z = Bv.to_int64 z in
    guard (fits_sext32 z);
    let z = Int64.to_int32_trunc z in
    let addr = Omem (Abd (y, z), mty xt) in
    [mov_typed xt addr (Oreg (x, xt))]
  ]

  let store_rrr_add_x_y_z env = [%rule
    let S.Treg (x, xt) = env.!["x"] in
    let S.Treg (y, _) = env.!["y"] in
    let S.Treg (z, _) = env.!["z"] in
    let addr = Omem (Abis (y, z, S1), mty xt) in
    [mov_typed xt addr (Oreg (x, xt))]
  ]

  let store_iri_add_x_y_z env = [%rule
    let S.Timm (x, xt) = env.!["x"] in
    let S.Treg (y, _) = env.!["y"] in
    let S.Timm (z, _) = env.!["z"] in
    let z = Bv.to_int64 z in
    guard (fits_sext32 z);
    let z = Int64.to_int32_trunc z in
    let@ o = with_imm xt (Bv.to_int64 x) xt in
    [I.mov (Omem (Abd (y, z), mty xt)) o]
  ]

  let store_f32ri_add_x_y_z env = [%rule
    let S.Tf32 x = env.!["x"] in
    let S.Treg (y, _) = env.!["y"] in
    let S.Timm (z, _) = env.!["z"] in
    let z = Bv.to_int64 z in
    guard (fits_sext32 z);
    let z = Int64.to_int32_trunc z in
    let* l, addr = fresh_label_addr in [
      I.movss (Omem (Abd (y, z), mty `f32)) (Omem (addr, `f32));
      I.fp32 l x
    ]
  ]

  let store_f64ri_add_x_y_z env = [%rule
    let S.Tf64 x = env.!["x"] in
    let S.Treg (y, _) = env.!["y"] in
    let S.Timm (z, _) = env.!["z"] in
    let z = Bv.to_int64 z in
    guard (fits_sext32 z);
    let z = Int64.to_int32_trunc z in
    let* l, addr = fresh_label_addr in [
      I.movsd (Omem (Abd (y, z), mty `f64)) (Omem (addr, `f64));
      I.fp64 l x
    ]
  ]

  let store_rsym_x_y env = [%rule
    let S.Tsym (s, o) = env.!["x"] in
    let S.Treg (y, yt) = env.!["y"] in
    let* x = fresh_reg in [
      lea_sym x s o;
      I.mov (Omem (Ab y, mty yt)) (Oreg (x, yt))
    ]
  ]

  let store_symr_x_y env = [%rule
    let S.Treg (x, xt) = env.!["x"] in
    let S.Tsym (s, o) = env.!["y"] in
    guard (sym_disp_fits o);
    [I.mov (Omem (Asym (s, o), mty xt)) (Oreg (x, xt))]
  ]

  let store_symi_x_y env = [%rule
    let S.Timm (x, xt) = env.!["x"] in
    let S.Tsym (s, o) = env.!["y"] in
    guard (sym_disp_fits o);
    let@ i = with_imm xt (Bv.to_int64 x) xt in
    [I.mov (Omem (Asym (s, o), mty xt)) i]
  ]

  (* Store a symbol's address (the value) to another symbol's address. Both
     are i64, since a symbol value is itself an address. *)
  let store_symsym_x_y env = [%rule
    let S.Tsym (s1, o1) = env.!["x"] in
    let S.Tsym (s2, o2) = env.!["y"] in
    let* tmp = fresh_reg in [
      lea_sym tmp s1 o1;
      I.mov (Omem (Asym (s2, o2), `i64)) (Oreg (tmp, `i64))
    ]
  ]

  let store_v_rr_x_y env = [%rule
    let S.Tvreg x = env.!["x"] in
    let S.Treg (y, _) = env.!["y"] in
    [I.movdqa (Omem (Ab y, `v128)) (Oregv x)]
  ]

  let store_v_rri_add_x_y_z env = [%rule
    let S.Tvreg x = env.!["x"] in
    let S.Treg (y, _) = env.!["y"] in
    let S.Timm (z, _) = env.!["z"] in
    let z = Bv.to_int64 z in
    guard (fits_sext32 z);
    let z = Int64.to_int32_trunc z in
    [I.movdqa (Omem (Abd (y, z), `v128)) (Oregv x)]
  ]

  (* `store x (y + z)`, dispatching on the forms of the stored value `x` and the
     offset `z` (the base `y` is always a register). *)
  let store_add_op env = [%rule
    match env.!["x"], env.!["z"] with
    | S.Treg _, S.Timm _ -> continue (store_rri_add_x_y_z env)
    | S.Timm _, S.Timm _ -> continue (store_iri_add_x_y_z env)
    | S.Tf32 _, S.Timm _ -> continue (store_f32ri_add_x_y_z env)
    | S.Tf64 _, S.Timm _ -> continue (store_f64ri_add_x_y_z env)
    | S.Treg _, S.Treg _ -> continue (store_rrr_add_x_y_z env)
    | _ -> fail
  ]

  (* `store x y`, dispatching on the forms of the stored value `x` and the
     address `y`. *)
  let store_op env = [%rule
    match env.!["x"], env.!["y"] with
    | S.Treg _, S.Treg _ -> continue (store_rr_x_y env)
    | S.Timm _, S.Treg _ -> continue (store_ri_x_y env)
    | S.Tsym _, S.Treg _ -> continue (store_rsym_x_y env)
    | S.Treg _, S.Tsym _ -> continue (store_symr_x_y env)
    | S.Timm _, S.Tsym _ -> continue (store_symi_x_y env)
    | S.Tsym _, S.Tsym _ -> continue (store_symsym_x_y env)
    | S.Tf32 _, S.Treg _ -> continue (store_rf32_x_y env)
    | S.Tf64 _, S.Treg _ -> continue (store_rf64_x_y env)
    | _ -> fail
  ]

  let mul_lea_ri_addi_x_y_z s env = [%rule
    let S.Treg (x, xt) = env.!["x"] in
    let S.Treg (y, _) = env.!["y"] in
    let S.Timm (z, _) = env.!["z"] in
    let z = Bv.to_int64 z in
    guard (fits_int32_pos z);
    guard (can_lea_ty xt);
    let z = Int64.to_int32_trunc z in
    [I.lea (Oreg (x, xt)) (Omem (Aisd (y, s, z), `i64))]
  ]

  (* `x = mul y z`, dispatching on the form of `z`. *)
  let imul env = [%rule
    let S.Treg (x, xt) = env.!["x"] in
    let S.Treg (y, yt) = env.!["y"] in
    match env.!["z"] with
    | S.Treg (z, zt) -> [
        I.mov (Oreg (x, xt)) (Oreg (y, yt));
        I.imul2 (Oreg (x, xt)) (Oreg (z, zt))
      ]
    | S.Timm (z, zt) ->
      let z = Bv.to_int64 z in
      if fits_imm xt z then
        [I.imul3 (Oreg (x, xt)) (Oreg (y, yt)) (Int64.to_int32_trunc z)]
      else
        let* z' = fresh_reg in [
          I.mov (Oreg (z', xt)) (Oimm (z, zt));
          I.mov (Oreg (x, xt)) (Oreg (y, yt));
          I.imul2 (Oreg (x, xt)) (Oreg (z', xt))
        ]
    | _ -> fail
  ]

  let imul8_rr_x_y_z env = [%rule
    let S.Treg (x, xt) = env.!["x"] in
    let S.Treg (y, yt) = env.!["y"] in
    let S.Treg (z, zt) = env.!["z"] in
    let rax = Rv.reg `rax in [
      I.movzx (Oreg (rax, `i16)) (Oreg (y, yt));
      I.imul1 (Oreg (z, zt));
      I.mov (Oreg (x, xt)) (Oreg (rax, `i8))
    ]
  ]

  (* `x = mulh y z` (signed high half), dispatching on the form of `z`. *)
  let imul_high env = [%rule
    let S.Treg (x, xt) = env.!["x"] in
    let S.Treg (y, yt) = env.!["y"] in
    let rax = Rv.reg `rax in
    let rdx = Rv.reg `rdx in
    match env.!["z"] with
    | S.Treg (z, zt) -> [
        I.mov (Oreg (rax, yt)) (Oreg (y, yt));
        I.imul1 (Oreg (z, zt));
        I.mov (Oreg (x, xt)) (Oreg (rdx, xt))
      ]
    | S.Timm (z, zt) ->
      let z = Bv.to_int64 z in
      begin match xt with
        | `i32 when fits_int32_pos z -> [
            I.movsxd (Oreg (x, `i64)) (Oreg (y, yt));
            I.imul3 (Oreg (x, `i64)) (Oreg (x, `i64)) (Int64.to_int32_trunc z);
            I.sar (Oreg (x, `i64)) (Oimm (32L, `i8))
          ]
        | _ -> [
            I.mov (Oreg (rax, bty zt)) (Oimm (z, zt));
            I.imul1 (Oreg (y, yt));
            I.mov (Oreg (x, xt)) (Oreg (rdx, xt))
          ]
      end
    | _ -> fail
  ]

  (* `x = mulh y z` at i8 (signed high byte via ah), on the form of `z`. *)
  let imul8_high env = [%rule
    let S.Treg (x, xt) = env.!["x"] in
    let S.Treg (y, yt) = env.!["y"] in
    let rax = Rv.reg `rax in
    match env.!["z"] with
    | S.Treg (z, zt) -> [
        I.movzx (Oreg (rax, `i16)) (Oreg (y, yt));
        I.imul1 (Oreg (z, zt));
        I.mov (Oreg (x, xt)) Oah
      ]
    | S.Timm (z, zt) ->
      let z = Bv.to_int64 z in [
        I.movzx (Oreg (rax, `i16)) (Oimm (z, zt));
        I.imul1 (Oreg (y, yt));
        I.mov (Oreg (x, xt)) Oah
      ]
    | _ -> fail
  ]

  (* `x = umulh y z` at i8 (unsigned high byte via ah), on the form of `z`. *)
  let mul8_high env = [%rule
    let S.Treg (x, xt) = env.!["x"] in
    let S.Treg (y, yt) = env.!["y"] in
    let rax = Rv.reg `rax in
    match env.!["z"] with
    | S.Treg (z, zt) -> [
        I.movzx (Oreg (rax, `i16)) (Oreg (y, yt));
        I.mul (Oreg (z, zt));
        I.mov (Oreg (x, xt)) Oah
      ]
    | S.Timm (z, zt) ->
      let z = Bv.to_int64 z in [
        I.movzx (Oreg (rax, `i16)) (Oimm (z, zt));
        I.mul (Oreg (y, yt));
        I.mov (Oreg (x, xt)) Oah
      ]
    | _ -> fail
  ]

  (* `x = umulh y z` (unsigned high half), dispatching on the form of `z`. *)
  let mul_high env = [%rule
    let S.Treg (x, xt) = env.!["x"] in
    let S.Treg (y, yt) = env.!["y"] in
    let rax = Rv.reg `rax in
    let rdx = Rv.reg `rdx in
    match env.!["z"] with
    | S.Treg (z, zt) -> [
        I.mov (Oreg (rax, yt)) (Oreg (y, yt));
        I.mul (Oreg (z, zt));
        I.mov (Oreg (x, xt)) (Oreg (rdx, xt))
      ]
    | S.Timm (z, zt) ->
      let z = Bv.to_int64 z in
      begin match xt with
        | `i32 when fits_int32 z && Int64.(z land 0x8000_0000L = 0L) -> [
            (* `umulh` is unsigned, so y must be zero-extended into its full 64-bit
               register before the 64-bit multiply. Its upper half is not guaranteed
               clear (it may share a register with a wider value). A 32-bit `mov`
               zero-extends. `z` has bit 31 clear here, so a signed `imul3` on the
               (now non-negative) operands still computes the correct product. If
               bit 31 is set, then we fall through to the `mul` (edx:eax) form. *)
            I.mov (Oreg (x, `i32)) (Oreg (y, `i32));
            I.imul3 (Oreg (x, `i64)) (Oreg (x, `i64)) (Int64.to_int32_trunc z);
            I.shr (Oreg (x, `i64)) (Oimm (32L, `i8))
          ]
        | _ -> [
            I.mov (Oreg (rax, bty zt)) (Oimm (z, zt));
            I.mul (Oreg (y, yt));
            I.mov (Oreg (x, xt)) (Oreg (rdx, xt))
          ]
      end
    | _ -> fail
  ]

  let float_rr_x_y_z f32 f64 env = [%rule
    let S.Treg (x, xt) = env.!["x"] in
    let S.Treg (y, yt) = env.!["y"] in
    let S.Treg (z, zt) = env.!["z"] in
    match xt with
    | `f64 -> [
        I.movsd (Oreg (x, xt)) (Oreg (y, yt));
        f64 (Oreg (x, xt)) (Oreg (z, zt))
      ]
    | `f32 -> [
        I.movss (Oreg (x, xt)) (Oreg (y, yt));
        f32 (Oreg (x, xt)) (Oreg (z, zt))
      ]
    | _ -> fail
  ] [@@specialise]

  (* `x = mul y z` at floating-point, dispatching on the form of `z`. *)
  let fmul env = [%rule
    match env.!["z"] with
    | S.Treg _ -> continue (float_rr_x_y_z I.mulss I.mulsd env)
    | S.Tf32 _ -> continue (arith_float_rf32 I.movss I.mulss I.fp32 env)
    | S.Tf64 _ -> continue (arith_float_rf64 I.movsd I.mulsd I.fp64 env)
    | _ -> fail
  ]

  let sign_rdx _rdx yt = cwd_cdq_cqo yt
  let zero_rdx rdx _yt = I.xor (Oreg (rdx, `i32)) (Oreg (rdx, `i32))

  (* `x = <div/rem> y z` at i16/i32/i64, dispatching on the operand forms.
     `setup` primes rdx (sign- or zero-extend), `op` is idiv/div, and `result`
     is rax (quotient) or rdx (remainder). *)
  let div_op setup op result env = [%rule
    let S.Treg (x, xt) = env.!["x"] in
    let rax = Rv.reg `rax in
    let rdx = Rv.reg `rdx in
    match env.!["y"], env.!["z"] with
    | S.Treg (y, yt), S.Treg (z, zt) -> [
        I.mov (Oreg (rax, yt)) (Oreg (y, yt));
        setup rdx yt;
        op (Oreg (z, zt));
        I.mov (Oreg (x, xt)) (Oreg (result, xt))
      ]
    | S.Treg (y, yt), S.Timm (z, zt) ->
      let* tmp = fresh_reg in [
        I.mov (Oreg (tmp, bty zt)) (Oimm (Bv.to_int64 z, zt));
        I.mov (Oreg (rax, yt)) (Oreg (y, yt));
        setup rdx yt;
        op (Oreg (tmp, bty zt));
        I.mov (Oreg (x, xt)) (Oreg (result, xt))
      ]
    | S.Timm (y, yt), S.Treg (z, zt) -> [
        I.mov (Oreg (rax, bty yt)) (Oimm (Bv.to_int64 y, yt));
        setup rdx (bty yt);
        op (Oreg (z, zt));
        I.mov (Oreg (x, xt)) (Oreg (result, xt))
      ]
    | _ -> fail
  ] [@@specialise]

  (* `x = <div/rem> y z` at i8: dividend goes through ax (movzx), `setup` primes
     the high part, `op` is idiv/div, and `result` selects al or ah. *)
  let div8_op ~setup ~op ~result env = [%rule
    let S.Treg (x, xt) = env.!["x"] in
    let rax = Rv.reg `rax in
    match env.!["y"], env.!["z"] with
    | S.Treg (y, yt), S.Treg (z, zt) -> [
        I.movzx (Oreg (rax, `i16)) (Oreg (y, yt));
        setup ();
        op (Oreg (z, zt));
        I.mov (Oreg (x, xt)) result
      ]
    | S.Treg (y, yt), S.Timm (z, zt) ->
      let* tmp = fresh_reg in [
        I.mov (Oreg (tmp, bty zt)) (Oimm (Bv.to_int64 z, zt));
        I.movzx (Oreg (rax, `i16)) (Oreg (y, yt));
        setup ();
        op (Oreg (tmp, bty zt));
        I.mov (Oreg (x, xt)) result
      ]
    | S.Timm (y, yt), S.Treg (z, zt) ->
      let* tmp = fresh_reg in [
        I.mov (Oreg (tmp, bty yt)) (Oimm (Bv.to_int64 y, yt));
        I.movzx (Oreg (rax, `i16)) (Oreg (tmp, bty yt));
        setup ();
        op (Oreg (z, zt));
        I.mov (Oreg (x, xt)) result
      ]
    | _ -> fail
  ] [@@specialise]

  (* `x = <div/rem> y z` at floating-point, dispatching on the operand forms. *)
  let fdiv env = [%rule
    match env.!["y"], env.!["z"] with
    | S.Treg _, S.Treg _ -> continue (float_rr_x_y_z I.divss I.divsd env)
    | S.Treg _, S.Tf32 _ -> continue (arith_float_rf32 I.movss I.divss I.fp32 env)
    | S.Treg _, S.Tf64 _ -> continue (arith_float_rf64 I.movsd I.divsd I.fp64 env)
    | S.Tf32 _, S.Treg _ -> continue (arith_float_fr32 I.movss I.divss I.fp32 env)
    | S.Tf64 _, S.Treg _ -> continue (arith_float_fr64 I.movsd I.divsd I.fp64 env)
    | _ -> fail
  ]

  (* Shift helpers.

     The `ext` mode controls whether and how the source is loaded
     into the destination:

     - [`narrow]: no promotion; operate at the IR type's width.
       Required for rotations (rol, ror) because rotation wraps at
       the type boundary.
     - [`nop]: promote narrow widths to i32 with plain mov. Correct
       for shl because upper-bit garbage doesn't affect the
       lower-width result.
     - [`zext]: promote with movzx. Required for shr so upper-bit
       garbage doesn't corrupt the lower bits after the shift.
     - [`sext]: promote with movsx. Required for sar so the sign
       fill is correct.
  *)

  let shift_dst_ty ~ext xt = match ext with
    | `nop | `zext | `sext -> promote_narrow_ty xt
    | `narrow -> xt

  let shift_mov_yx ~ext (x : Rv.t) xt (y : Rv.t) yt =
    let xt' = shift_dst_ty ~ext xt in
    match ext, xt with
    | `zext, (`i8 | `i16) -> I.movzx (Oreg (x, xt')) (Oreg (y, yt))
    | `sext, (`i8 | `i16) -> I.movsx (Oreg (x, xt')) (Oreg (y, yt))
    | (`nop | `zext | `sext), _ -> I.mov (Oreg (x, xt')) (Oreg (y, xt'))
    | `narrow, _ -> I.mov (Oreg (x, xt)) (Oreg (y, yt))

  (* Shift/rotate `x = y <op> z`, dispatching on the forms of the value `y`
     and the shift count `z`:

     - `~ext` controls how a narrow `y` is widened before the shift
     - `~lea` enables the `x = y << 1` -> `lea` special case for `lsl`
     - `shift_dst_ty ~ext:`nop` already equals `promote_narrow_ty`,
       so the non-`lea` path here reproduces the old `lsl_ri` exactly
  *)
  let shift ?(lea = false) ~ext i env = [%rule
    let S.Treg (x, xt) = env.!["x"] in
    let rcx = Rv.reg `rcx in
    match env.!["y"], env.!["z"] with
    | S.Treg (y, yt), S.Treg (z, _) ->
      let xt' = shift_dst_ty ~ext xt in [
        shift_mov_yx ~ext x xt y yt;
        I.mov (Oreg (rcx, `i8)) (Oreg (z, `i8));
        i (Oreg (x, xt')) (Oreg (rcx, `i8))
      ]
    | S.Timm (y, yt), S.Treg (z, _) ->
      let y = Bv.to_int64 y in
      (* For sar on narrow widths, pre-compute the sign-extended value
         so the imm placed in the i32 register has the correct sign
         fill. For shl/shr, `mov r32, imm32` already zero-extends a
         narrow bitvector correctly. *)
      let y = match ext, yt with
        | `sext, `i8 when Int64.(y land 0x80L <> 0L) ->
          Int64.(y lor 0xFFFFFF00L)
        | `sext, `i16 when Int64.(y land 0x8000L <> 0L) ->
          Int64.(y lor 0xFFFF0000L)
        | _ -> y in
      let xt_shift = shift_dst_ty ~ext xt in
      (* i64 imm that fits `int32` is loaded at i32 to save the REX.W
         prefix. The subsequent shift still runs at i64. For narrow
         promoted shifts, load the imm at i32. For sar the value was
         already sign-extended above; for shl/shr the narrow-range
         imm is naturally zero-extended by `mov r32, imm32`. *)
      let xt_mov, yt_mov = match ext, xt with
        | _, `i64 when fits_uint32 y -> `i32, `i32
        | (`nop | `zext | `sext), (`i8 | `i16) -> xt_shift, `i32
        | _ -> xt_shift, yt in [
        I.mov (Oreg (x, xt_mov)) (Oimm (y, yt_mov));
        I.mov (Oreg (rcx, `i8)) (Oreg (z, `i8));
        i (Oreg (x, xt_shift)) (Oreg (rcx, `i8))
      ]
    | S.Treg (y, yt), S.Timm (z, _) ->
      let z = Bv.to_int64 z in
      if lea && Int64.(z = 1L) && can_lea_ty xt then
        [I.lea (Oreg (x, xt)) (Omem (Abis (y, y, S1), `i64))]
      else
        let xt' = shift_dst_ty ~ext xt in [
          shift_mov_yx ~ext x xt y yt;
          i (Oreg (x, xt')) (Oimm (Int64.(z land 0xFFL), `i8))
        ]
    | _ -> fail
  ] [@@specialise]

  let neg_r_x_y env = [%rule
    let S.Treg (x, xt) = env.!["x"] in
    let S.Treg (y, _)  = env.!["y"] in
    let xt' = promote_narrow_ty xt in [
      I.mov (Oreg (x, xt')) (Oreg (y, xt'));
      I.neg (Oreg (x, xt'))
    ]
  ]

  let fneg_r_x_y env = [%rule
    let S.Treg (x, xt) = env.!["x"] in
    let S.Treg (y, yt) = env.!["y"] in
    match xt with
    | `f32 ->
      let f = Float32.of_bits 0x8000_0000l in
      let* l, addr = fresh_label_addr in [
        I.movss (Oreg (x, xt)) (Oreg (y, yt));
        I.xorps (Oreg (x, xt)) (Omem (addr, `v128));
        I.fp32v l f
      ]
    | `f64 ->
      let f = float_of_bits 0x8000_0000_0000_0000L in
      let* l, addr = fresh_label_addr in [
        I.movsd (Oreg (x, xt)) (Oreg (y, yt));
        I.xorpd (Oreg (x, xt)) (Omem (addr, `v128));
        I.fp64v l f
      ]
    | _ -> fail
  ]

  (* `x = fneg y`. The only needed form is `Treg`, since the
     `f32/f64` constant one would have been folded. *)
  let fneg_unary = fneg_r_x_y

  let not_r_x_y env = [%rule
    let S.Treg (x, xt) = env.!["x"] in
    let S.Treg (y, _)  = env.!["y"] in
    let xt' = promote_narrow_ty xt in [
      I.mov (Oreg (x, xt')) (Oreg (y, xt'));
      I.not_ (Oreg (x, xt'))
    ]
  ]

  let clz_r_x_y env = [%rule
    let S.Treg (x, xt) = env.!["x"] in
    let n = Int64.of_int (Type.sizeof_basic xt - 1) in
    let S.Treg (y, yt) = env.!["y"] in
    let Some (movinst, ty, ity) = match xt with
      | #Type.imm as imm ->
        begin match imm with
          | `i8 | `i16 -> Some (I.movzx, `i32, `i32)
          | `i32 | `i64 -> Some (I.mov, xt, imm)
        end
      | _ -> None in
    let* tmp1 = fresh_reg in
    let* tmp2 = fresh_reg in [
      movinst (Oreg (tmp1, ty)) (Oreg (y, yt));
      I.bsr (Oreg (tmp2, ty)) (Oreg (tmp1, ty));
      I.xor (Oreg (tmp2, ty)) (Oimm (n, ity));
      I.mov (Oreg (x, ty)) (Oreg (tmp2, ty))
    ]
  ]

  let ctz_r_x_y env = [%rule
    let S.Treg (x, xt) = env.!["x"] in
    let S.Treg (y, yt) = env.!["y"] in
    let Some (movinst, ty) = match xt with
      | `i8 | `i16 -> Some (I.movzx, `i32)
      | `i32 | `i64 -> Some (I.mov, xt)
      | _ -> None in
    let* tmp1 = fresh_reg in
    let* tmp2 = fresh_reg in [
      movinst (Oreg (tmp1, ty)) (Oreg (y, yt));
      I.bsf (Oreg (tmp2, ty)) (Oreg (tmp1, ty));
      I.mov (Oreg (x, ty)) (Oreg (tmp2, ty))
    ]
  ]

  let popcnt_r_x_y env = [%rule
    let S.Treg (x, xt) = env.!["x"] in
    let S.Treg (y, yt) = env.!["y"] in
    let Some (movinst, ty) = match xt with
      | `i8 | `i16 -> Some (I.movzx, `i32)
      | `i32 | `i64 -> Some (I.mov, xt)
      | _ -> None in
    let* tmp1 = fresh_reg in
    let* tmp2 = fresh_reg in [
      movinst (Oreg (tmp1, ty)) (Oreg (y, yt));
      I.popcnt (Oreg (tmp2, ty)) (Oreg (tmp1, ty));
      I.mov (Oreg (x, ty)) (Oreg (tmp2, ty))
    ]
  ]

  let bswap_r_x_y env = [%rule
    let S.Treg (x, xt) = env.!["x"] in
    let S.Treg (y, yt) = env.!["y"] in
    match xt with
    | `i16 ->
      (* `bswap r16` is officially undefined; swap the byte pair with a
         rotate instead. *) [
        I.mov (Oreg (x, xt)) (Oreg (y, yt));
        I.rol (Oreg (x, xt)) (Oimm (8L, `i8))
      ]
    | `i32 | `i64 -> [
        I.mov (Oreg (x, xt)) (Oreg (y, yt));
        I.bswap (Oreg (x, xt))
      ]
    | _ -> fail
  ]

  let sext_rr_x_y env = [%rule
    let S.Treg (x, xt) = env.!["x"] in
    let S.Treg (y, yt) = env.!["y"] in
    match xt, yt with
    | `i64, `i32 ->
      [I.movsxd (Oreg (x, xt)) (Oreg (y, yt))]
    | (#Type.imm as xi), (#Type.imm as yi)
      when Type.sizeof_imm xi > Type.sizeof_imm yi ->
      [I.movsx (Oreg (x, xt)) (Oreg (y, yt))]
    | #Type.imm, #Type.imm ->
      let xt' = promote_narrow_ty xt in
      [I.mov (Oreg (x, xt')) (Oreg (y, xt'))]
    | _ -> fail
  ]

  let fext_rr_x_y ty env = [%rule
    let S.Treg (x, xt) = env.!["x"] in
    let S.Treg (y, yt) = env.!["y"] in
    match ty, xt, yt with
    | `f32, `f32, `f32 ->
      [I.movss (Oreg (x, xt)) (Oreg (y, yt))]
    | `f64, `f64, `f64 ->
      [I.movsd (Oreg (x, xt)) (Oreg (y, yt))]
    | `f64, `f64, `f32 -> [
        I.xorpd (Oreg (x, xt)) (Oreg (x, xt));
        I.cvtss2sd (Oreg (x, xt)) (Oreg (y, yt))
      ]
    | _ -> fail
  ]

  (* `x = fext y` to `ty`. The only needed form is `Treg`, since
     the `f32/f64` constant forms would have been folded by now. *)
  let fext_unary = fext_rr_x_y

  let fibits_rr_x_y ty env = [%rule
    let S.Treg (x, xt) = env.!["x"] in
    let S.Treg (y, yt) = env.!["y"] in
    match ty, xt, yt with
    | `f32, `f32, `i32 ->
      [I.movd (Oreg (x, xt)) (Oreg (y, yt))]
    | `f64, `f64, `i64 ->
      [I.movq (Oreg (x, xt)) (Oreg (y, yt))]
    | _ -> fail
  ]

  let ftosi_rr_x_y tf ti env = [%rule
    let S.Treg (x, xt) = env.!["x"] in
    let S.Treg (y, yt) = env.!["y"] in
    guard (Type.equal_basic (bty ti) xt);
    guard (Type.equal_basic (bty tf) yt);
    let xt' = ftosi_ty xt in
    match tf with
    | `f32 ->
      let@ sext = extbh ~signed:true x xt' xt in
      I.cvttss2si (Oreg (x, xt')) (Oreg (y, yt)) :: sext
    | `f64 ->
      let@ sext = extbh ~signed:true x xt' xt in
      I.cvttsd2si (Oreg (x, xt')) (Oreg (y, yt)) :: sext
    | _ -> fail
  ]

  (* Handles the 64-bit integer case where 2^63 would saturate cvttss2si/cvttsd2si. *)
  let ftoui_rr_i64 cvtts movf subf ucomif embed x y yt =
    let* l, addr = fresh_label_addr in
    let* tmp_r = C.Var.fresh >>| Rv.var in
    let* tmp_fp = C.Var.fresh >>| Rv.var in
    let* tmp_r2 = C.Var.fresh >>| Rv.var in
    let@ oz = with_imm `i64 Int64.min_value `i64 in !![
      cvtts (Oreg (tmp_r, `i64)) (Oreg (y, yt));
      movf (Oreg (tmp_fp, yt)) (Oreg (y, yt));
      subf (Oreg (tmp_fp, yt)) (Omem (addr, mty yt));
      cvtts (Oreg (tmp_r2, `i64)) (Oreg (tmp_fp, yt));
      I.xor (Oreg (tmp_r2, `i64)) oz;
      ucomif (Oreg (y, yt)) (Omem (addr, mty yt));
      I.cmov Cae (Oreg (tmp_r, `i64)) (Oreg (tmp_r2, `i64));
      I.mov (Oreg (x, `i64)) (Oreg (tmp_r, `i64));
      embed l;
    ]

  let ftoui_rr_x_y tf ti env = [%rule
    let S.Treg (x, xt) = env.!["x"] in
    let S.Treg (y, yt) = env.!["y"] in
    guard (Type.equal_basic (bty ti) xt);
    guard (Type.equal_basic (bty tf) yt);
    let xt' = ftoui_ty xt in
    match tf, xt with
    | `f32, `i64 ->
      let threshold = Float32.of_float (2.0 ** 63.0) in
      continue (
        ftoui_rr_i64
          I.cvttss2si I.movss I.subss I.ucomiss
          (fun l -> I.fp32 l threshold) x y yt)
    | `f64, `i64 ->
      let threshold = 2.0 ** 63.0 in
      continue (
        ftoui_rr_i64
          I.cvttsd2si I.movsd I.subsd I.ucomisd
          (fun l -> I.fp64 l threshold) x y yt)
    | `f32, _ ->
      let@ zext = extbh x xt' xt in
      I.cvttss2si (Oreg (x, xt')) (Oreg (y, yt)) :: zext
    | `f64, _ ->
      let@ zext = extbh x xt' xt in
      I.cvttsd2si (Oreg (x, xt')) (Oreg (y, yt)) :: zext
    | _ -> fail
  ]

  let ftrunc_rr_x_y ty env = [%rule
    let S.Treg (x, xt) = env.!["x"] in
    let S.Treg (y, yt) = env.!["y"] in
    match ty, xt, yt with
    | `f64, `f64, `f64 ->
      [I.movsd (Oreg (x, xt)) (Oreg (y, yt))]
    | `f32, `f32, `f32 ->
      [I.movss (Oreg (x, xt)) (Oreg (y, yt))]
    | `f32, `f32, `f64 -> [
        I.xorps (Oreg (x, xt)) (Oreg (x, xt));
        I.cvtsd2ss (Oreg (x, xt)) (Oreg (y, yt))
      ]
    | _ -> fail
  ]

  (* `x = ftrunc y` to `ty`. The only needed form is `Treg`, since
     the `f32/f64` constant would have been folded. *)
  let ftrunc_unary = ftrunc_rr_x_y

  let ifbits_rr_x_y ty env = [%rule
    let S.Treg (x, xt) = env.!["x"] in
    let S.Treg (y, yt) = env.!["y"] in
    guard (Type.equal_basic (bty ty) xt);
    match ty, yt with
    | `i32, `f32 ->
      [I.movd (Oreg (x, xt)) (Oreg (y, yt))]
    | `i64, `f64 ->
      [I.movq (Oreg (x, xt)) (Oreg (y, yt))]
    | _ -> fail
  ]

  (* `x = ifbits y` to `ty`. The only needed form is `Treg`, since
     the `f32/f64` constant would have been folded. *)
  let ifbits_unary = ifbits_rr_x_y

  let itrunc_rr_x_y ty env = [%rule
    let S.Treg (x, xt) = env.!["x"] in
    let S.Treg (y, _) = env.!["y"] in
    guard (Type.equal_basic (bty ty) xt);
    (* Assume the width of the destination. *)
    [I.mov (Oreg (x, xt)) (Oreg (y, xt))]
  ]

  let sitof_rr_x_y ti tf env = [%rule
    let S.Treg (x, xt) = env.!["x"] in
    let S.Treg (y, yt) = env.!["y"] in
    guard (Type.equal_basic (bty tf) xt);
    guard (Type.equal_basic (bty ti) yt);
    match ti, tf with
    | (`i8 | `i16), `f32 ->
      let* tmp = fresh_reg in [
        I.movsx (Oreg (tmp, `i32)) (Oreg (y, yt));
        I.xorps (Oreg (x, xt)) (Oreg (x, xt));
        I.cvtsi2ss (Oreg (x, xt)) (Oreg (tmp, `i32))
      ]
    | `i32, `f32 -> [
        I.xorps (Oreg (x, xt)) (Oreg (x, xt));
        I.cvtsi2ss (Oreg (x, xt)) (Oreg (y, yt))
      ]
    | `i64, `f32 -> [
        I.xorps (Oreg (x, xt)) (Oreg (x, xt));
        I.cvtsi2ss (Oreg (x, xt)) (Oreg (y, yt))
      ]
    | (`i8 | `i16), `f64 ->
      let* tmp = fresh_reg in [
        I.movsx (Oreg (tmp, `i32)) (Oreg (y, yt));
        I.xorpd (Oreg (x, xt)) (Oreg (x, xt));
        I.cvtsi2sd (Oreg (x, xt)) (Oreg (tmp, `i32))
      ]
    | `i32, `f64 -> [
        I.xorpd (Oreg (x, xt)) (Oreg (x, xt));
        I.cvtsi2sd (Oreg (x, xt)) (Oreg (y, yt))
      ]
    | `i64, `f64 -> [
        I.xorpd (Oreg (x, xt)) (Oreg (x, xt));
        I.cvtsi2sd (Oreg (x, xt)) (Oreg (y, yt))
      ]
  ]

  let call_sym_x_y env = [%rule
    let S.Tcall args = env.!["x"] in
    let S.Tsym (s, o) = env.!["y"] in
    [I.call args (Osym (s, o))]
  ]

  let call_r_x_y env = [%rule
    let S.Tcall args = env.!["x"] in
    let S.Treg (y, yt) = env.!["y"] in
    [I.call args (Oreg (y, yt))]
  ]

  let tailcall_sym_x_y env = [%rule
    let S.Tcall args = env.!["x"] in
    let S.Tsym (s, o) = env.!["y"] in
    [I.tailcall args (Osym (s, o))]
  ]

  let tailcall_r_x_y env = [%rule
    let S.Tcall args = env.!["x"] in
    let S.Treg (y, yt) = env.!["y"] in
    [I.tailcall args (Oreg (y, yt))]
  ]

  (* `call/tailcall args -> target`, dispatching on the form of the target `y`. *)
  let call_op env = [%rule
    match env.!["y"] with
    | S.Tsym _ -> continue (call_sym_x_y env)
    | S.Treg _ -> continue (call_r_x_y env)
    | _ -> fail
  ]

  let tailcall_op env = [%rule
    match env.!["y"] with
    | S.Tsym _ -> continue (tailcall_sym_x_y env)
    | S.Treg _ -> continue (tailcall_r_x_y env)
    | _ -> fail
  ]

  (* The actual dispatch logic for a jump table. *)
  let jmp_tbl_impl d tbl x (xt : Type.imm) =
    let xtb = bty xt in
    let tbl, lowest, highest = adjust_table d tbl in
    let highest' = Int64.(highest - lowest) in
    let diff = Int64.(highest - highest') in
    let diff_fits = fits_int32_pos diff in
    let* tdiff = if diff_fits then !!None else
        let+ r = C.Var.fresh >>| Rv.var in
        Some r in
    let* tl, tladdr = fresh_label_addr in
    let* tbase = C.Var.fresh >>| Rv.var in
    let* tidx = C.Var.fresh >>| Rv.var in
    let+ tdst = C.Var.fresh >>| Rv.var in
    List.concat [
      ( (* Compare against the lowest value, if necessary. *)
        if Int64.(lowest = 1L) then [
          I.test (Oreg (x, xtb)) (Oreg (x, xtb));
          I.jcc Ce d;
        ]
        else if Int64.(lowest > 0L) then [
          I.cmp (Oreg (x, xtb)) (Oimm (lowest, xt));
          I.jcc Cb d;
        ]
        else []
      );
      [ (* Zero-extend the index. *)
        match xt with
        | `i8 | `i16 ->
          I.movzx (Oreg (tidx, `i64)) (Oreg (x, xtb))
        | `i32 ->
          (* i32 has implicit zero-extension. *)
          I.mov_ (Oreg (tidx, xtb)) (Oreg (x, xtb))
        | `i64 ->
          I.mov (Oreg (tidx, xtb)) (Oreg (x, xtb))
      ];
      ( (* Subtract the difference from the index if needed. *)
        match diff with
        | 0L -> []
        | 1L -> [I.dec (Oreg (tidx, `i64))]
        | _ when diff_fits ->
          [I.sub (Oreg (tidx, `i64)) (Oimm (diff, `i64))]
        | _ ->
          let tdiff = Option.value_exn tdiff in [
            I.mov (Oreg (tdiff, `i64)) (Oimm (diff, `i64));
            I.sub (Oreg (tidx, `i64)) (Oreg (tdiff, `i64));
          ]
      );
      [ (* Compare against highest value. *)
        I.cmp (Oreg (tidx, `i64)) (Oimm (highest', `i64));
        I.jcc Ca d;
        (* Get the base of the table. *)
        I.lea (Oreg (tbase, `i64)) (Omem (tladdr, `i64));
        (* Jump to the table entry. *)
        I.movsxd (Oreg (tdst, `i64)) (Omem (Abis (tbase, tidx, S4), `i32));
        I.add (Oreg (tdst, `i64)) (Oreg (tbase, `i64));
        I.jmp (Jind (Oreg (tdst, `i64)));
        (* The table itself. *)
        I.jmptbl tl tbl;
      ]
    ]

  let jmp_tbl_x_y env = [%rule
    let S.Treg (x, xt) = env.!["x"] in
    let S.Ttbl (d, tbl) = env.!["y"] in
    match xt, tbl with
    | _, [] ->
      (* Just jump to the default label. *)
      [I.jmp (Jlbl d)]
    | #Type.fp, _ ->
      (* Should be impossible. *)
      fail
    | #Type.imm as xt, _ ->
      continue (jmp_tbl_impl d tbl x xt)
  ]

  open P.Op

  (* One instruction-selection callback per op. Each dispatches on the matched
     operand forms and emits the corresponding instruction sequence. *)
  module Sel = struct
    let add = add_binop
    let sub = sub_binop

    let and_ = bitwise ~trunc:true I.and_
    let or_ = bitwise I.or_
    let xor = bitwise I.xor

    let lsl_ = shift ~lea:true ~ext:`nop I.shl
    let lsr_ = shift ~ext:`zext I.shr
    let asr_ = shift ~ext:`sext I.sar
    let rol = shift ~ext:`narrow I.rol
    let ror = shift ~ext:`narrow I.ror

    let mul = imul
    let mul8 = imul8_rr_x_y_z
    let fmul = fmul
    let mulh = imul_high
    let mulh8 = imul8_high
    let umulh = mul_high
    let umulh8 = mul8_high

    let div = div_op sign_rdx I.idiv (Rv.reg `rax)
    let fdiv = fdiv
    let div8 = div8_op ~setup:(fun () -> I.cwd) ~op:I.idiv ~result:(Oreg (Rv.reg `rax, `i8))
    let rem = div_op sign_rdx I.idiv (Rv.reg `rdx)
    let rem8 = div8_op ~setup:(fun () -> I.cwd) ~op:I.idiv ~result:Oah
    let udiv = div_op zero_rdx I.div (Rv.reg `rax)
    let urem = div_op zero_rdx I.div (Rv.reg `rdx)

    let urem8 =
      div8_op ~op:I.div ~result:Oah
        ~setup:(fun () ->
            let rdx = Rv.reg `rdx in
            I.xor (Oreg (rdx, `i32)) (Oreg (rdx, `i32)))

    let setcc_test = setcc_test
    let setcc = setcc

    let sel_f32 = sel_f32_x_y_z
    let sel_f64 = sel_f64_x_y_z
    let sel_fcmp32 = sel_fcmp32
    let sel_fcmp64 = sel_fcmp64
    let setcc_f32 = setcc_f32
    let setcc_f64 = setcc_f64
    let sel = sel_cmov
    let sel_zero = sel_zero

    let load = load_basic
    let load_add = load_add
    let load_sext = load_sext
    let load_zext = load_zext
    let load_sext_add = load_sext_add
    let load_zext_add = load_zext_add
    let load_sext_add_mul = load_sext_add_mul_rr_scale_x_y_z
    let load_zext_add_mul = load_zext_add_mul_rr_scale_x_y_z
    let load_sext_add_mul_disp = load_sext_add_mul_rr_scale_imm_x_y_z_w
    let load_zext_add_mul_disp = load_zext_add_mul_rr_scale_imm_x_y_z_w
    let load_sext_add_mul_disp_neg = load_sext_add_mul_rr_scale_neg_imm_x_y_z_w
    let load_zext_add_mul_disp_neg = load_zext_add_mul_rr_scale_neg_imm_x_y_z_w

    let move_ri = move_reg_imm ~zx:false
    let move = move_unary
    let neg = neg_r_x_y
    let fneg = fneg_unary
    let not_ = not_r_x_y
    let clz = clz_r_x_y
    let ctz = ctz_r_x_y
    let popcnt = popcnt_r_x_y
    let bswap = bswap_r_x_y
    let sext = sext_rr_x_y
    let zext = move_reg_imm ~zx:true
    let fext = fext_unary
    let fibits = fibits_rr_x_y
    let ftosi = ftosi_rr_x_y
    let ftoui = ftoui_rr_x_y
    let ftrunc = ftrunc_unary
    let ifbits = ifbits_unary
    let itrunc = itrunc_rr_x_y
    let sitof = sitof_rr_x_y

    let store_add = store_add_op
    let store = store_op
    let store_vec_add = store_v_rri_add_x_y_z
    let store_vec_basic = store_v_rr_x_y

    let jmp = jmp_op
    let br_test = br_test
    let br_icmp = br_icmp
    let br_fcmp32 = br_fcmp32
    let br_fcmp64 = br_fcmp64
    let call = call_op
    let tailcall = tailcall_op
  end

  (* The rules themselves. *)
  module Rules = struct
    let add_mul_lea_tbl = [
      `i16, i16 0,  i16 1,  i16 2,  i16 3,  i16 4,  i16 8;
      `i32, i32 0l, i32 1l, i32 2l, i32 3l, i32 4l, i32 8l;
      `i64, i64 0L, i64 1L, i64 2L, i64 3L, i64 4L, i64 8L;
    ]

    let sib_disp_pat ty sm ss =
      let ty' = bty ty in [|
        add ty' (add ty' y (mul ty' z sm)) w;
        add ty' y (add ty' (mul ty' z sm) w);
        add ty' (add ty' y (lsl_ ty z ss)) w;
        add ty' y (add ty' (lsl_ ty z ss) w);
      |]

    let sib_disp_neg_pat ty sm ss =
      let ty' = bty ty in [|
        sub ty' (add ty' y (mul ty' z sm)) w;
        add ty' y (sub ty' (mul ty' z sm) w);
        sub ty' (add ty' y (lsl_ ty z ss)) w;
        add ty' y (sub ty' (lsl_ ty z ss) w);
      |]

    let sib_pat ty sm ss =
      let ty' = bty ty in [|
        add ty' y (mul ty' z sm);
        add ty' y (lsl_ ty z ss);
      |]

    let si_disp_pat ty sm ss =
      let ty' = bty ty in [|
        add ty' (mul ty' y sm) z;
        add ty' (lsl_ ty y ss) z;
      |]

    let sib_disp_i64 = [|
      sib_disp_pat `i64 (i64 1L) (i64 0L);
      sib_disp_pat `i64 (i64 2L) (i64 1L);
      sib_disp_pat `i64 (i64 4L) (i64 2L);
      sib_disp_pat `i64 (i64 8L) (i64 3L);
    |]

    let sib_disp_neg_i64 = [|
      sib_disp_neg_pat `i64 (i64 1L) (i64 0L);
      sib_disp_neg_pat `i64 (i64 2L) (i64 1L);
      sib_disp_neg_pat `i64 (i64 4L) (i64 2L);
      sib_disp_neg_pat `i64 (i64 8L) (i64 3L);
    |]

    let sib_i64 = [|
      sib_pat `i64 (i64 1L) (i64 0L);
      sib_pat `i64 (i64 2L) (i64 1L);
      sib_pat `i64 (i64 4L) (i64 2L);
      sib_pat `i64 (i64 8L) (i64 3L);
    |]

    (* x = add (add y (mul z i)) w => lea x, [y+z*i+w]

       where i \in {1,2,4,8} and w is a constant

       x = add (add y (lsl z i)) w => lea x, [y+z*(1<<i)+w]

       where i \in {0,1,2,3} and w is a constant
    *)
    let add_mul_lea_imm =
      add_mul_lea_tbl >* fun (ty, zero, one, two, three, four, eight) ->
        let p1 = sib_disp_pat ty one zero in
        let p2 = sib_disp_pat ty two one in
        let p3 = sib_disp_pat ty four two in
        let p4 = sib_disp_pat ty eight three in
        let ty' = bty ty in [
          (* Scale by 8 *)
          move x p4.(0) => add_mul_rr_scale_imm_x_y_z_w S8;
          move x p4.(1) => add_mul_rr_scale_imm_x_y_z_w S8;
          move x p4.(2) => add_mul_rr_scale_imm_x_y_z_w S8;
          move x p4.(3) => add_mul_rr_scale_imm_x_y_z_w S8;
          (* Scale by 4 *)
          move x p3.(0) => add_mul_rr_scale_imm_x_y_z_w S4;
          move x p3.(1) => add_mul_rr_scale_imm_x_y_z_w S4;
          move x p3.(2) => add_mul_rr_scale_imm_x_y_z_w S4;
          move x p3.(3) => add_mul_rr_scale_imm_x_y_z_w S4;
          (* Scale by 2 *)
          move x p2.(0) => add_mul_rr_scale_imm_x_y_z_w S2;
          move x p2.(1) => add_mul_rr_scale_imm_x_y_z_w S2;
          move x p2.(2) => add_mul_rr_scale_imm_x_y_z_w S2;
          move x p2.(3) => add_mul_rr_scale_imm_x_y_z_w S2;
          (* Scale by 1 *)
          move x p1.(0) => add_mul_rr_scale_imm_x_y_z_w S1;
          move x p1.(1) => add_mul_rr_scale_imm_x_y_z_w S1;
          move x p1.(2) => add_mul_rr_scale_imm_x_y_z_w S1;
          move x p1.(3) => add_mul_rr_scale_imm_x_y_z_w S1;
          move x (add ty' (add ty' y z) w) => add_mul_rr_scale_imm_x_y_z_w S1;
          move x (add ty' y (add ty' z w)) => add_mul_rr_scale_imm_x_y_z_w S1;
        ]

    (* x = sub (add y (mul z i)) w => lea x, [y+z*i-w]

       where i \in {1,2,4,8} and w is a constant

       x = sub (add y (lsl z i)) w => lea x, [y+z*(1<<i)-w]

       where i \in {0,1,2,3} and w is a constant
    *)
    let add_mul_lea_neg_imm =
      add_mul_lea_tbl >* fun (ty, zero, one, two, three, four, eight) ->
        let p1 = sib_disp_neg_pat ty one zero in
        let p2 = sib_disp_neg_pat ty two one in
        let p3 = sib_disp_neg_pat ty four two in
        let p4 = sib_disp_neg_pat ty eight three in
        let ty' = bty ty in [
          (* Scale by 8 *)
          move x p4.(0) => add_mul_rr_scale_neg_imm_x_y_z_w S8;
          move x p4.(1) => add_mul_rr_scale_neg_imm_x_y_z_w S8;
          move x p4.(2) => add_mul_rr_scale_neg_imm_x_y_z_w S8;
          move x p4.(3) => add_mul_rr_scale_neg_imm_x_y_z_w S8;
          (* Scale by 4 *)
          move x p3.(0) => add_mul_rr_scale_neg_imm_x_y_z_w S4;
          move x p3.(1) => add_mul_rr_scale_neg_imm_x_y_z_w S4;
          move x p3.(2) => add_mul_rr_scale_neg_imm_x_y_z_w S4;
          move x p3.(3) => add_mul_rr_scale_neg_imm_x_y_z_w S4;
          (* Scale by 2 *)
          move x p2.(0) => add_mul_rr_scale_neg_imm_x_y_z_w S2;
          move x p2.(1) => add_mul_rr_scale_neg_imm_x_y_z_w S2;
          move x p2.(2) => add_mul_rr_scale_neg_imm_x_y_z_w S2;
          move x p2.(3) => add_mul_rr_scale_neg_imm_x_y_z_w S2;
          (* Scale by 1 *)
          move x p1.(0) => add_mul_rr_scale_neg_imm_x_y_z_w S1;
          move x p1.(1) => add_mul_rr_scale_neg_imm_x_y_z_w S1;
          move x p1.(2) => add_mul_rr_scale_neg_imm_x_y_z_w S1;
          move x p1.(3) => add_mul_rr_scale_neg_imm_x_y_z_w S1;
          move x (sub ty' (add ty' y z) w) => add_mul_rr_scale_neg_imm_x_y_z_w S1;
        ]

    (* x = add y (mul z i) => lea x, [y+z*i]

       where i \in {1,2,4,8}

       x = add y (lsl z i) => lea x, [y+z*(1<<i)]

       where i \in {0,1,2,3}
    *)
    let add_mul_lea =
      add_mul_lea_tbl >* fun (ty, zero, one, two, three, four, eight) ->
        let p1 = sib_pat ty one zero in
        let p2 = sib_pat ty two one in
        let p3 = sib_pat ty four two in
        let p4 = sib_pat ty eight three in [
          (* Scale by 8 *)
          move x p4.(0) => add_mul_rr_scale_x_y_z S8;
          move x p4.(1) => add_mul_rr_scale_x_y_z S8;
          (* Scale by 4 *)
          move x p3.(0) => add_mul_rr_scale_x_y_z S4;
          move x p3.(1) => add_mul_rr_scale_x_y_z S4;
          (* Scale by 2 *)
          move x p2.(0) => add_mul_rr_scale_x_y_z S2;
          move x p2.(1) => add_mul_rr_scale_x_y_z S2;
          (* Scale by 1 *)
          move x p1.(0) => add_mul_rr_scale_x_y_z S1;
          move x p1.(1) => add_mul_rr_scale_x_y_z S1;
        ]

    (* x = add y, z *)
    let add_basic = [
      move x (add `i8  y z) => Sel.add;
      move x (add `i16 y z) => Sel.add;
      move x (add `i32 y z) => Sel.add;
      move x (add `i64 y z) => Sel.add;
      move x (add `f32 y z) => Sel.add;
      move x (add `f64 y z) => Sel.add;
    ]

    (* x = sub y z *)
    let sub_basic = [
      move x (sub `i8  y z) => Sel.sub;
      move x (sub `i16 y z) => Sel.sub;
      move x (sub `i32 y z) => Sel.sub;
      move x (sub `i64 y z) => Sel.sub;
      move x (sub `f32 y z) => Sel.sub;
      move x (sub `f64 y z) => Sel.sub;
    ]

    (* x = and y, z *)
    let and_basic = [
      move x (and_ `i8  y z) => Sel.and_;
      move x (and_ `i16 y z) => Sel.and_;
      move x (and_ `i32 y z) => Sel.and_;
      move x (and_ `i64 y z) => Sel.and_;
    ]

    (* x = or y, z *)
    let or_basic = [
      move x (or_ `i8  y z) => Sel.or_;
      move x (or_ `i16 y z) => Sel.or_;
      move x (or_ `i32 y z) => Sel.or_;
      move x (or_ `i64 y z) => Sel.or_;
    ]

    (* x = xor y, z *)
    let xor_basic = [
      move x (xor `i8  y z) => Sel.xor;
      move x (xor `i16 y z) => Sel.xor;
      move x (xor `i32 y z) => Sel.xor;
      move x (xor `i64 y z) => Sel.xor;
    ]

    (* x = lsl y, z *)
    let lsl_basic = [
      move x (lsl_ `i8  y z) => Sel.lsl_;
      move x (lsl_ `i16 y z) => Sel.lsl_;
      move x (lsl_ `i32 y z) => Sel.lsl_;
      move x (lsl_ `i64 y z) => Sel.lsl_;
    ]

    (* x = lsr y, z *)
    let lsr_basic = [
      move x (lsr_ `i8  y z) => Sel.lsr_;
      move x (lsr_ `i16 y z) => Sel.lsr_;
      move x (lsr_ `i32 y z) => Sel.lsr_;
      move x (lsr_ `i64 y z) => Sel.lsr_;
    ]

    (* x = asr y, z *)
    let asr_basic = [
      move x (asr_ `i8  y z) => Sel.asr_;
      move x (asr_ `i16 y z) => Sel.asr_;
      move x (asr_ `i32 y z) => Sel.asr_;
      move x (asr_ `i64 y z) => Sel.asr_;
    ]

    (* x = rol y, z *)
    let rol_basic = [
      move x (rol `i8  y z) => Sel.rol;
      move x (rol `i16 y z) => Sel.rol;
      move x (rol `i32 y z) => Sel.rol;
      move x (rol `i64 y z) => Sel.rol;
    ]

    (* x = ror y, z *)
    let ror_basic = [
      move x (ror `i8  y z) => Sel.ror;
      move x (ror `i16 y z) => Sel.ror;
      move x (ror `i32 y z) => Sel.ror;
      move x (ror `i64 y z) => Sel.ror;
    ]

    (*  x = add (mul y i) z => lea x, [y*i+z]

        where i \in {1,2,4,8}
    *)
    let mul_lea_add_imm =
      add_mul_lea_tbl >* fun (ty, zero, one, two, three, four, eight) ->
        let p1 = si_disp_pat ty one zero in
        let p2 = si_disp_pat ty two one in
        let p3 = si_disp_pat ty four two in
        let p4 = si_disp_pat ty eight three in [
          (* Scale by 8 *)
          move x p4.(0) => mul_lea_ri_addi_x_y_z S8;
          move x p4.(1) => mul_lea_ri_addi_x_y_z S8;
          (* Scale by 4 *)
          move x p3.(0) => mul_lea_ri_addi_x_y_z S4;
          move x p3.(1) => mul_lea_ri_addi_x_y_z S4;
          (* Scale by 2 *)
          move x p2.(0) => mul_lea_ri_addi_x_y_z S2;
          move x p2.(1) => mul_lea_ri_addi_x_y_z S2;
          (* Scale by 1 *)
          move x p1.(0) => add_ri_x_y_z;
          move x p1.(1) => add_ri_x_y_z;
        ]

    (* x = mul y, z *)
    let mul_basic = [
      move x (mul `i8  y z) => Sel.mul8;
      move x (mul `i16 y z) => Sel.mul;
      move x (mul `i32 y z) => Sel.mul;
      move x (mul `i64 y z) => Sel.mul;
      move x (mul `f32 y z) => Sel.fmul;
      move x (mul `f64 y z) => Sel.fmul;
    ]

    (* x = mulh y, z *)
    let mulh_basic = [
      move x (mulh `i8  y z) => Sel.mulh8;
      move x (mulh `i16 y z) => Sel.mulh;
      move x (mulh `i32 y z) => Sel.mulh;
      move x (mulh `i64 y z) => Sel.mulh;
    ]

    (* x = umulh y, z *)
    let umulh_basic = [
      move x (umulh `i8  y z) => Sel.umulh8;
      move x (umulh `i16 y z) => Sel.umulh;
      move x (umulh `i32 y z) => Sel.umulh;
      move x (umulh `i64 y z) => Sel.umulh;
    ]

    (* x = div y, z *)
    let div_basic = [
      move x (div `i8  y z) => Sel.div8;
      move x (div `i16 y z) => Sel.div;
      move x (div `i32 y z) => Sel.div;
      move x (div `i64 y z) => Sel.div;
      move x (div `f32 y z) => Sel.fdiv;
      move x (div `f64 y z) => Sel.fdiv;
    ]

    (* x = rem y, z *)
    let rem_basic = [
      move x (rem `i8  y z) => Sel.rem8;
      move x (rem `i16 y z) => Sel.rem;
      move x (rem `i32 y z) => Sel.rem;
      move x (rem `i64 y z) => Sel.rem;
    ]

    (* x = udiv y, z *)
    let udiv_basic = [
      move x (udiv `i16 y z) => Sel.udiv;
      move x (udiv `i32 y z) => Sel.udiv;
      move x (udiv `i64 y z) => Sel.udiv;
    ]

    (* x = urem y, z *)
    let urem_basic = [
      move x (urem `i8  y z) => Sel.urem8;
      move x (urem `i16 y z) => Sel.urem;
      move x (urem `i32 y z) => Sel.urem;
      move x (urem `i64 y z) => Sel.urem;
    ]

    (* x = y == 0
       x = y != 0
    *)
    let setcc_zero = [
      `i8,  i8  0;
      `i16, i16 0;
      `i32, i32 0l;
      `i64, i64 0L;
    ] >* fun (ty, zero) ->
        let ty' = bty ty in [
          move x (ne ty' (and_ ty y z) zero) => Sel.setcc_test (); (* x = (y & z) != 0 *)
          move x (eq ty' (and_ ty y z) zero) => Sel.setcc_test () ~neg:true; (* x = (y & z) == 0 *)
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
          move x (eq ty' y z) => Sel.setcc Ce;
          move x (ne ty' y z) => Sel.setcc Cne;
          (* Unsigned *)
          move x (lt ty' y z) => Sel.setcc Cb;
          move x (le ty' y z) => Sel.setcc Cbe;
          move x (gt ty' y z) => Sel.setcc Ca;
          move x (ge ty' y z) => Sel.setcc Cae;
          (* Signed *)
          move x (slt ty y z) => Sel.setcc Cl;
          move x (sle ty y z) => Sel.setcc Cle;
          move x (sgt ty y z) => Sel.setcc Cg;
          move x (sge ty y z) => Sel.setcc Cge;
        ]

    (* x = fcmp y, z *)
    let setcc_fbasic = [
      `f32, Sel.setcc_f32;
      `f64, Sel.setcc_f64
    ] >* fun (ty, f) ->
        let ty' = bty ty in [
          (* Equality *)
          move x (eq ty' y z) => f Ce;
          move x (ne ty' y z) => f Cne;
          (* Comparison *)
          move x (lt ty' y z) => f Cb;
          move x (le ty' y z) => f Cbe;
          move x (gt ty' y z) => f Ca;
          move x (ge ty' y z) => f Cae;
          (* Ordering *)
          move x (uo ty y z) => f Cp;
          move x (o ty y z) => f Cnp;
        ]

    let sel_zero = [
      `i8,  i8  0;
      `i16, i16 0;
      `i32, i32 0l;
      `i64, i64 0L;
    ] >* fun (tyc, zero) ->
        [`i8; `i16; `i32; `i64] >* fun tys ->
          let tys' = bty tys in
          let tyc' = bty tyc in [
            move x (sel tys' (eq tyc' y zero) yes no) => Sel.sel_zero ();
            move x (sel tys' (ne tyc' y zero) yes no) => Sel.sel_zero ~neg:true ();
            move x (sel tys' (slt tyc y zero) yes no) => Sel.sel_zero ~eq:false ();
            move x (sel tys' (sge tyc y zero) yes no) => Sel.sel_zero ~neg:true ~eq:false ();
          ]

    (* x = sel (fcmp y z) yes no  [f32/f64 comparison, f32/f64 select value] *)
    let sel_fbasic = [
      `f32, Sel.sel_f32;
      `f64, Sel.sel_f64;
    ] >* fun (ty, f) ->
        let ty' = bty ty in [
          move x (sel ty' (eq ty' y z) yes no) => f FEQ;
          move x (sel ty' (ne ty' y z) yes no) => f FNEQ;
          move x (sel ty' (lt ty' y z) yes no) => f FLT;
          move x (sel ty' (le ty' y z) yes no) => f FLE;
          move x (sel ty' (gt ty' y z) yes no) => f FNLT;
          move x (sel ty' (ge ty' y z) yes no) => f FNLE;
          move x (sel ty' (uo ty  y z) yes no) => f FUNORD;
          move x (sel ty' (o ty   y z) yes no) => f FORD;
        ]

    (* x = sel (fcmp y z) yes no  [f32/f64 comparison, integer select value].

       The condition codes match `setcc_fbasic` (ucomi sets CF/ZF/PF).
    *)
    let sel_ifcmp =
      [`i8; `i16; `i32; `i64] >* fun tys -> [
          `f32, Sel.sel_fcmp32;
          `f64, Sel.sel_fcmp64;
        ] >* fun (fty, f) ->
          let tys' = bty tys in
          let fty' = bty fty in [
            move x (sel tys' (eq fty' y z) yes no) => f Ce;
            move x (sel tys' (ne fty' y z) yes no) => f Cne;
            move x (sel tys' (lt fty' y z) yes no) => f Cb;
            move x (sel tys' (le fty' y z) yes no) => f Cbe;
            move x (sel tys' (gt fty' y z) yes no) => f Ca;
            move x (sel tys' (ge fty' y z) yes no) => f Cae;
            move x (sel tys' (uo fty  y z) yes no) => f Cp;
            move x (sel tys' (o fty   y z) yes no) => f Cnp;
          ]

    (* x = sel (cmp y z) yes no *)
    let sel_ibasic =
      [`i8; `i16; `i32; `i64] >* fun tyc ->
        [`i8; `i16; `i32; `i64] >* fun tys ->
          let tys' = bty tys in
          let tyc' = bty tyc in [
            (* Equality *)
            move x (sel tys' (eq tyc' y z) yes no) => Sel.sel Ce;
            move x (sel tys' (ne tyc' y z) yes no) => Sel.sel Cne;
            (* Unsigned *)
            move x (sel tys' (lt tyc' y z) yes no) => Sel.sel Cb;
            move x (sel tys' (le tyc' y z) yes no) => Sel.sel Cbe;
            move x (sel tys' (gt tyc' y z) yes no) => Sel.sel Ca;
            move x (sel tys' (ge tyc' y z) yes no) => Sel.sel Cae;
            (* Signed *)
            move x (sel tys' (slt tyc y z) yes no) => Sel.sel Cl;
            move x (sel tys' (sle tyc y z) yes no) => Sel.sel Cle;
            move x (sel tys' (sgt tyc y z) yes no) => Sel.sel Cg;
            move x (sel tys' (sge tyc y z) yes no) => Sel.sel Cge;
          ]

    (* x = load (add (add y (mul z i)) w) => mov x, [y+z*i+w]

       where i \in {1,2,4,8} and w is a constant

       x = load (add (add y (lsl z i)) w) => mov x, [y+z*(1<<i)+w]

       where i \in {0,1,2,3} and w is a constant
    *)
    let load_add_mul_disp =
      [`i8; `i16; `i32; `i64; `f32; `f64] >* fun ty ->
        let p1 = sib_disp_i64.(0) in
        let p2 = sib_disp_i64.(1) in
        let p3 = sib_disp_i64.(2) in
        let p4 = sib_disp_i64.(3) in [
          (* Scale by 8 *)
          move x (load ty p4.(0)) => load_add_mul_rr_scale_imm_x_y_z_w S8;
          move x (load ty p4.(1)) => load_add_mul_rr_scale_imm_x_y_z_w S8;
          move x (load ty p4.(2)) => load_add_mul_rr_scale_imm_x_y_z_w S8;
          move x (load ty p4.(3)) => load_add_mul_rr_scale_imm_x_y_z_w S8;
          (* Scale by 4 *)
          move x (load ty p3.(0)) => load_add_mul_rr_scale_imm_x_y_z_w S4;
          move x (load ty p3.(1)) => load_add_mul_rr_scale_imm_x_y_z_w S4;
          move x (load ty p3.(2)) => load_add_mul_rr_scale_imm_x_y_z_w S4;
          move x (load ty p3.(3)) => load_add_mul_rr_scale_imm_x_y_z_w S4;
          (* Scale by 2 *)
          move x (load ty p2.(0)) => load_add_mul_rr_scale_imm_x_y_z_w S2;
          move x (load ty p2.(1)) => load_add_mul_rr_scale_imm_x_y_z_w S2;
          move x (load ty p2.(2)) => load_add_mul_rr_scale_imm_x_y_z_w S2;
          move x (load ty p2.(3)) => load_add_mul_rr_scale_imm_x_y_z_w S2;
          (* Scale by 1 *)
          move x (load ty p1.(0)) => load_add_mul_rr_scale_imm_x_y_z_w S1;
          move x (load ty p1.(1)) => load_add_mul_rr_scale_imm_x_y_z_w S1;
          move x (load ty p1.(2)) => load_add_mul_rr_scale_imm_x_y_z_w S1;
          move x (load ty p1.(3)) => load_add_mul_rr_scale_imm_x_y_z_w S1;
          move x (load ty (add ty (add ty y z) w)) => load_add_mul_rr_scale_imm_x_y_z_w S1;
          move x (load ty (add ty y (add ty z w))) => load_add_mul_rr_scale_imm_x_y_z_w S1;
        ]

    (* x = load (sub (add y (mul z i)) w) => mov x, [y+z*i-w]

       where i \in {1,2,4,8} and w is a constant

       x = load (sub (add y (lsl z i)) w) => mov x, [y+z*(1<<i)-w]

       where i \in {0,1,2,3} and w is a constant
    *)
    let load_add_mul_disp_neg =
      [`i8; `i16; `i32; `i64; `f32; `f64] >* fun ty ->
        let p1 = sib_disp_neg_i64.(0) in
        let p2 = sib_disp_neg_i64.(1) in
        let p3 = sib_disp_neg_i64.(2) in
        let p4 = sib_disp_neg_i64.(3) in [
          (* Scale by 8 *)
          move x (load ty p4.(0)) => load_add_mul_rr_scale_neg_imm_x_y_z_w S8;
          move x (load ty p4.(1)) => load_add_mul_rr_scale_neg_imm_x_y_z_w S8;
          move x (load ty p4.(2)) => load_add_mul_rr_scale_neg_imm_x_y_z_w S8;
          move x (load ty p4.(3)) => load_add_mul_rr_scale_neg_imm_x_y_z_w S8;
          (* Scale by 4 *)
          move x (load ty p3.(0)) => load_add_mul_rr_scale_neg_imm_x_y_z_w S4;
          move x (load ty p3.(1)) => load_add_mul_rr_scale_neg_imm_x_y_z_w S4;
          move x (load ty p3.(2)) => load_add_mul_rr_scale_neg_imm_x_y_z_w S4;
          move x (load ty p3.(3)) => load_add_mul_rr_scale_neg_imm_x_y_z_w S4;
          (* Scale by 2 *)
          move x (load ty p2.(0)) => load_add_mul_rr_scale_neg_imm_x_y_z_w S2;
          move x (load ty p2.(1)) => load_add_mul_rr_scale_neg_imm_x_y_z_w S2;
          move x (load ty p2.(2)) => load_add_mul_rr_scale_neg_imm_x_y_z_w S2;
          move x (load ty p2.(3)) => load_add_mul_rr_scale_neg_imm_x_y_z_w S2;
          (* Scale by 1 *)
          move x (load ty p1.(0)) => load_add_mul_rr_scale_neg_imm_x_y_z_w S1;
          move x (load ty p1.(1)) => load_add_mul_rr_scale_neg_imm_x_y_z_w S1;
          move x (load ty p1.(2)) => load_add_mul_rr_scale_neg_imm_x_y_z_w S1;
          move x (load ty p1.(3)) => load_add_mul_rr_scale_neg_imm_x_y_z_w S1;
          move x (load ty (sub ty (add ty y z) w)) => load_add_mul_rr_scale_neg_imm_x_y_z_w S1;
        ]

    (* x = load (add y (mul z i)) => mov x, [y+z*i]

       where i \in {1,2,4,8}

       x = load (add y (lsl z i)) => mov x, [y+z*(1<<i)]

       where i \in {0,1,2,3}
    *)
    let load_add_mul =
      [`i8; `i16; `i32; `i64; `f32; `f64] >* fun ty ->
        let p1 = sib_i64.(0) in
        let p2 = sib_i64.(1) in
        let p3 = sib_i64.(2) in
        let p4 = sib_i64.(3) in [
          (* Scale by 8 *)
          move x (load ty p4.(0)) => load_add_mul_rr_scale_x_y_z S8;
          move x (load ty p4.(1)) => load_add_mul_rr_scale_x_y_z S8;
          (* Scale by 4 *)
          move x (load ty p3.(0)) => load_add_mul_rr_scale_x_y_z S4;
          move x (load ty p3.(1)) => load_add_mul_rr_scale_x_y_z S4;
          (* Scale by 2 *)
          move x (load ty p2.(0)) => load_add_mul_rr_scale_x_y_z S2;
          move x (load ty p2.(1)) => load_add_mul_rr_scale_x_y_z S2;
          (* Scale by 1 *)
          move x (load ty p1.(0)) => load_add_mul_rr_scale_x_y_z S1;
          move x (load ty p1.(1)) => load_add_mul_rr_scale_x_y_z S1;
        ]

    (* x = load (add y, z) *)
    let load_add = [
      move x (load `i8  (add `i64 y z)) => Sel.load_add;
      move x (load `i16 (add `i64 y z)) => Sel.load_add;
      move x (load `i32 (add `i64 y z)) => Sel.load_add;
      move x (load `i64 (add `i64 y z)) => Sel.load_add;
      move x (load `f32 (add `i64 y z)) => Sel.load_add;
      move x (load `f64 (add `i64 y z)) => Sel.load_add;
    ]

    (* x = load y *)
    let load_basic = [
      move x (load `i8  y) => Sel.load;
      move x (load `i16 y) => Sel.load;
      move x (load `i32 y) => Sel.load;
      move x (load `i64 y) => Sel.load;
      move x (load `f32 y) => Sel.load;
      move x (load `f64 y) => Sel.load;
    ]

    let load_ext_pairs : (Type.imm * Type.imm) list = [
      `i16, `i8;
      `i32, `i8; `i32, `i16;
      `i64, `i8; `i64, `i16; `i64, `i32;
    ]

    (* x = sext/zext (load (add y z)) => movsx/movsxd/movzx x, [y+z] *)
    let load_ext_add =
      load_ext_pairs >* fun (xt, zt) -> [
          sext, Sel.load_sext_add;
          zext, Sel.load_zext_add
        ] >* fun (p, f) ->
          let zt' = bty zt in [
            move x (p xt (load zt' (add `i64 y z))) => f zt;
          ]

    (* x = sext/zext (load (add (add y (mul z i)) w)) => movsx/movsxd/movzx x, [y+z*i+w] *)
    let load_ext_add_mul_disp =
      load_ext_pairs >* fun (xt, zt) -> [
          sext, Sel.load_sext_add_mul_disp;
          zext, Sel.load_zext_add_mul_disp
        ] >* fun (p, f) ->
          let zt' = bty zt in
          let p1 = sib_disp_i64.(0) in
          let p2 = sib_disp_i64.(1) in
          let p3 = sib_disp_i64.(2) in
          let p4 = sib_disp_i64.(3) in [
            (* Scale by 8 *)
            move x (p xt (load zt' p4.(0))) => f zt S8;
            move x (p xt (load zt' p4.(1))) => f zt S8;
            move x (p xt (load zt' p4.(2))) => f zt S8;
            move x (p xt (load zt' p4.(3))) => f zt S8;
            (* Scale by 4 *)
            move x (p xt (load zt' p3.(0))) => f zt S4;
            move x (p xt (load zt' p3.(1))) => f zt S4;
            move x (p xt (load zt' p3.(2))) => f zt S4;
            move x (p xt (load zt' p3.(3))) => f zt S4;
            (* Scale by 2 *)
            move x (p xt (load zt' p2.(0))) => f zt S2;
            move x (p xt (load zt' p2.(1))) => f zt S2;
            move x (p xt (load zt' p2.(2))) => f zt S2;
            move x (p xt (load zt' p2.(3))) => f zt S2;
            (* Scale by 1 *)
            move x (p xt (load zt' p1.(0))) => f zt S1;
            move x (p xt (load zt' p1.(1))) => f zt S1;
            move x (p xt (load zt' p1.(2))) => f zt S1;
            move x (p xt (load zt' p1.(3))) => f zt S1;
            move x (p xt (load zt' (add `i64 (add `i64 y z) w))) => f zt S1;
            move x (p xt (load zt' (add `i64 y (add `i64 z w)))) => f zt S1;
          ]

    (* x = sext/zext (load (sub (add y (mul z i)) w)) => movsx/movsxd/movzx x, [y+z*i-w] *)
    let load_ext_add_mul_disp_neg =
      load_ext_pairs >* fun (xt, zt) -> [
          sext, Sel.load_sext_add_mul_disp_neg;
          zext, Sel.load_zext_add_mul_disp_neg
        ] >* fun (p, f) ->
          let zt' = bty zt in
          let p1 = sib_disp_neg_i64.(0) in
          let p2 = sib_disp_neg_i64.(1) in
          let p3 = sib_disp_neg_i64.(2) in
          let p4 = sib_disp_neg_i64.(3) in [
            (* Scale by 8 *)
            move x (p xt (load zt' p4.(0))) => f zt S8;
            move x (p xt (load zt' p4.(1))) => f zt S8;
            move x (p xt (load zt' p4.(2))) => f zt S8;
            move x (p xt (load zt' p4.(3))) => f zt S8;
            (* Scale by 4 *)
            move x (p xt (load zt' p3.(0))) => f zt S4;
            move x (p xt (load zt' p3.(1))) => f zt S4;
            move x (p xt (load zt' p3.(2))) => f zt S4;
            move x (p xt (load zt' p3.(3))) => f zt S4;
            (* Scale by 2 *)
            move x (p xt (load zt' p2.(0))) => f zt S2;
            move x (p xt (load zt' p2.(1))) => f zt S2;
            move x (p xt (load zt' p2.(2))) => f zt S2;
            move x (p xt (load zt' p2.(3))) => f zt S2;
            (* Scale by 1 *)
            move x (p xt (load zt' p1.(0))) => f zt S1;
            move x (p xt (load zt' p1.(1))) => f zt S1;
            move x (p xt (load zt' p1.(2))) => f zt S1;
            move x (p xt (load zt' p1.(3))) => f zt S1;
            move x (p xt (load zt' (sub `i64 (add `i64 y z) w))) => f zt S1;
          ]

    (* x = sext/zext (load (add y (mul z i))) => movsx/movsxd/movzx x, [y+z*i] *)
    let load_ext_add_mul =
      load_ext_pairs >* fun (xt, zt) -> [
          sext, Sel.load_sext_add_mul;
          zext, Sel.load_zext_add_mul
        ] >* fun (p, f) ->
          let zt' = bty zt in
          let p1 = sib_i64.(0) in
          let p2 = sib_i64.(1) in
          let p3 = sib_i64.(2) in
          let p4 = sib_i64.(3) in [
            (* Scale by 8 *)
            move x (p xt (load zt' p4.(0))) => f zt S8;
            move x (p xt (load zt' p4.(1))) => f zt S8;
            (* Scale by 4 *)
            move x (p xt (load zt' p3.(0))) => f zt S4;
            move x (p xt (load zt' p3.(1))) => f zt S4;
            (* Scale by 2 *)
            move x (p xt (load zt' p2.(0))) => f zt S2;
            move x (p xt (load zt' p2.(1))) => f zt S2;
            (* Scale by 1 *)
            move x (p xt (load zt' p1.(0))) => f zt S1;
            move x (p xt (load zt' p1.(1))) => f zt S1;
          ]

    (* x = sext/zext (load y) => movsx/movsxd/movzx x, [y] *)
    let load_ext_basic =
      load_ext_pairs >* fun (xt, zt) -> [
          sext, Sel.load_sext;
          zext, Sel.load_zext
        ] >* fun (p, f) ->
          let zt' = bty zt in [
            move x (p xt (load zt' y)) => f zt;
          ]

    (* x = neg y *)
    let neg_basic = [
      move x (neg `i8  y) => Sel.neg;
      move x (neg `i16 y) => Sel.neg;
      move x (neg `i32 y) => Sel.neg;
      move x (neg `i64 y) => Sel.neg;
      move x (neg `f32 y) => Sel.fneg;
      move x (neg `f64 y) => Sel.fneg;
    ]

    (* x = not y *)
    let not_basic = [
      move x (not_ `i8  y) => Sel.not_;
      move x (not_ `i16 y) => Sel.not_;
      move x (not_ `i32 y) => Sel.not_;
      move x (not_ `i64 y) => Sel.not_;
    ]

    (* x = clz y *)
    let clz_basic = [
      move x (clz `i8  y) => Sel.clz;
      move x (clz `i16 y) => Sel.clz;
      move x (clz `i32 y) => Sel.clz;
      move x (clz `i64 y) => Sel.clz;
    ]

    (* x = ctz y *)
    let ctz_basic = [
      move x (ctz `i8  y) => Sel.ctz;
      move x (ctz `i16 y) => Sel.ctz;
      move x (ctz `i32 y) => Sel.ctz;
      move x (ctz `i64 y) => Sel.ctz;
    ]

    (* x = popcnt y *)
    let popcnt_basic = [
      move x (popcnt `i8  y) => Sel.popcnt;
      move x (popcnt `i16 y) => Sel.popcnt;
      move x (popcnt `i32 y) => Sel.popcnt;
      move x (popcnt `i64 y) => Sel.popcnt;
    ]

    (* x = bswap y *)
    let bswap_basic = [
      move x (bswap `i16 y) => Sel.bswap;
      move x (bswap `i32 y) => Sel.bswap;
      move x (bswap `i64 y) => Sel.bswap;
    ]

    (* x = sext y *)
    let sext_basic = [
      move x (sext `i8  y) => Sel.move_ri;
      move x (sext `i16 y) => Sel.sext;
      move x (sext `i32 y) => Sel.sext;
      move x (sext `i64 y) => Sel.sext;
    ]

    (* x = zext y *)
    let zext_basic = [
      move x (zext `i8  y) => Sel.move_ri;
      move x (zext `i16 y) => Sel.zext;
      move x (zext `i32 y) => Sel.zext;
      move x (zext `i64 y) => Sel.zext;
    ]

    (* x = fext y *)
    let fext_basic = [
      move x (fext `f32 y) => Sel.fext `f32;
      move x (fext `f64 y) => Sel.fext `f64;
    ]

    (* x = fibits y *)
    let fibits_basic = [
      move x (fibits `f32 y) => Sel.fibits `f32;
      move x (fibits `f64 y) => Sel.fibits `f64;
    ]

    (* x = ftosi y *)
    let ftosi_basic =
      [`i8; `i16; `i32; `i64] >* fun ty ->
        let ty' = ity ty in [
          move x (ftosi `f64 ty' y) => Sel.ftosi `f64 ty;
          move x (ftosi `f32 ty' y) => Sel.ftosi `f32 ty;
        ]

    (* x = ftoui y *)
    let ftoui_basic =
      [`i8; `i16; `i32; `i64] >* fun ty ->
        let ty' = ity ty in [
          move x (ftoui `f64 ty' y) => Sel.ftoui `f64 ty;
          move x (ftoui `f32 ty' y) => Sel.ftoui `f32 ty;
        ]

    (* x = ftrunc y *)
    let ftrunc_basic = [
      move x (ftrunc `f32 y) => Sel.ftrunc `f32;
      move x (ftrunc `f64 y) => Sel.ftrunc `f64;
    ]

    (* x = ifbits y *)
    let ifbits_basic = [
      move x (ifbits `i32 y) => Sel.ifbits `i32;
      move x (ifbits `i64 y) => Sel.ifbits `i64;
    ]

    (* x = itrunc y *)
    let itrunc_basic =
      [`i8; `i16; `i32; `i64] >* fun ty -> [
          move x (itrunc ty y) => Sel.itrunc ty;
        ]

    (* x = sitof y *)
    let sitof_basic =
      [`i8; `i16; `i32; `i64] >* fun ty -> [
          move x (sitof ty `f32 y) => Sel.sitof ty `f32;
          move x (sitof ty `f64 y) => Sel.sitof ty `f64;
        ]

    (* x = flag y

       This ends up being just a move. We handle the cases that
       bind boolean-typed variables directly.
    *)
    let flag_basic =
      [`i8; `i16; `i32; `i64] >* fun ty -> [
          move x (flag ty y) => flag_to_reg
        ]

    (* x = y *)
    let move_basic = [
      move x y => Sel.move;
    ]

    (* store x, xmmword ptr [y+z] *)
    let store_vec_add = [
      store `v128 x (add `i64 y z) => Sel.store_vec_add;
    ]

    (* store x, xmmword ptr [y] *)
    let store_vec_basic = [
      store `v128 x y => Sel.store_vec_basic;
    ]

    (* store x (add (add y (mul z i)) w) => mov [y+z*i+w], x

       where i \in {1,2,4,8} and w is a constant

       store x (add (add y (lsl z i)) w) => mov [y+z*(1<<i)+w], x

       where i \in {0,1,2,3} and w is a constant
    *)
    let store_add_mul_disp =
      [`i8; `i16; `i32; `i64; `f32; `f64] >* fun ty ->
        let p1 = sib_disp_i64.(0) in
        let p2 = sib_disp_i64.(1) in
        let p3 = sib_disp_i64.(2) in
        let p4 = sib_disp_i64.(3) in [
          (* Scale by 8 *)
          store ty x p4.(0) => store_add_mul_rr_scale_imm_x_y_z_w S8;
          store ty x p4.(1) => store_add_mul_rr_scale_imm_x_y_z_w S8;
          store ty x p4.(2) => store_add_mul_rr_scale_imm_x_y_z_w S8;
          store ty x p4.(3) => store_add_mul_rr_scale_imm_x_y_z_w S8;
          (* Scale by 4 *)
          store ty x p3.(0) => store_add_mul_rr_scale_imm_x_y_z_w S4;
          store ty x p3.(1) => store_add_mul_rr_scale_imm_x_y_z_w S4;
          store ty x p3.(2) => store_add_mul_rr_scale_imm_x_y_z_w S4;
          store ty x p3.(3) => store_add_mul_rr_scale_imm_x_y_z_w S4;
          (* Scale by 2 *)
          store ty x p2.(0) => store_add_mul_rr_scale_imm_x_y_z_w S2;
          store ty x p2.(1) => store_add_mul_rr_scale_imm_x_y_z_w S2;
          store ty x p2.(2) => store_add_mul_rr_scale_imm_x_y_z_w S2;
          store ty x p2.(3) => store_add_mul_rr_scale_imm_x_y_z_w S2;
          (* Scale by 1 *)
          store ty x p1.(0) => store_add_mul_rr_scale_imm_x_y_z_w S1;
          store ty x p1.(1) => store_add_mul_rr_scale_imm_x_y_z_w S1;
          store ty x p1.(2) => store_add_mul_rr_scale_imm_x_y_z_w S1;
          store ty x p1.(3) => store_add_mul_rr_scale_imm_x_y_z_w S1;
          store ty x (add `i64 (add `i64 y z) w) => store_add_mul_rr_scale_imm_x_y_z_w S1;
          store ty x (add `i64 y (add `i64 z w)) => store_add_mul_rr_scale_imm_x_y_z_w S1;
        ]


    (* store x (sub (add y (mul z i)) w) => mov [y+z*i-w], x

       where i \in {1,2,4,8} and w is a constant

       store x (sub (add y (lsl z i)) w) => mov [y+z*(1<<i)-w], x

       where i \in {0,1,2,3} and w is a constant
    *)
    let store_add_mul_disp_neg =
      [`i8; `i16; `i32; `i64; `f32; `f64] >* fun ty ->
        let p1 = sib_disp_neg_i64.(0) in
        let p2 = sib_disp_neg_i64.(1) in
        let p3 = sib_disp_neg_i64.(2) in
        let p4 = sib_disp_neg_i64.(3) in [
          (* Scale by 8 *)
          store ty x p4.(0) => store_add_mul_rr_scale_neg_imm_x_y_z_w S8;
          store ty x p4.(1) => store_add_mul_rr_scale_neg_imm_x_y_z_w S8;
          store ty x p4.(2) => store_add_mul_rr_scale_neg_imm_x_y_z_w S8;
          store ty x p4.(3) => store_add_mul_rr_scale_neg_imm_x_y_z_w S8;
          (* Scale by 4 *)
          store ty x p3.(0) => store_add_mul_rr_scale_neg_imm_x_y_z_w S4;
          store ty x p3.(1) => store_add_mul_rr_scale_neg_imm_x_y_z_w S4;
          store ty x p3.(2) => store_add_mul_rr_scale_neg_imm_x_y_z_w S4;
          store ty x p3.(3) => store_add_mul_rr_scale_neg_imm_x_y_z_w S4;
          (* Scale by 2 *)
          store ty x p2.(0) => store_add_mul_rr_scale_neg_imm_x_y_z_w S2;
          store ty x p2.(1) => store_add_mul_rr_scale_neg_imm_x_y_z_w S2;
          store ty x p2.(2) => store_add_mul_rr_scale_neg_imm_x_y_z_w S2;
          store ty x p2.(3) => store_add_mul_rr_scale_neg_imm_x_y_z_w S2;
          (* Scale by 1 *)
          store ty x p1.(0) => store_add_mul_rr_scale_neg_imm_x_y_z_w S1;
          store ty x p1.(1) => store_add_mul_rr_scale_neg_imm_x_y_z_w S1;
          store ty x p1.(2) => store_add_mul_rr_scale_neg_imm_x_y_z_w S1;
          store ty x p1.(3) => store_add_mul_rr_scale_neg_imm_x_y_z_w S1;
          store ty x (sub `i64 (add `i64 y z) w) => store_add_mul_rr_scale_neg_imm_x_y_z_w S1;
        ]

    (* store x (add y (mul z i)) => mov [y+z*i], x

       where i \in {1,2,4,8}

       store x (add y (lsl z i)) => mov [y+z*(1<<i)], x

       where i \in {0,1,2,3}
    *)
    let store_add_mul =
      [`i8; `i16; `i32; `i64; `f32; `f64] >* fun ty ->
        let p1 = sib_i64.(0) in
        let p2 = sib_i64.(1) in
        let p3 = sib_i64.(2) in
        let p4 = sib_i64.(3) in [
          (* Scale by 8 *)
          store ty x p4.(0) => store_add_mul_rr_scale_x_y_z S8;
          store ty x p4.(1) => store_add_mul_rr_scale_x_y_z S8;
          (* Scale by 4 *)
          store ty x p3.(0) => store_add_mul_rr_scale_x_y_z S4;
          store ty x p3.(1) => store_add_mul_rr_scale_x_y_z S4;
          (* Scale by 2 *)
          store ty x p2.(0) => store_add_mul_rr_scale_x_y_z S2;
          store ty x p2.(1) => store_add_mul_rr_scale_x_y_z S2;
          (* Scale by 1 *)
          store ty x p1.(0) => store_add_mul_rr_scale_x_y_z S1;
          store ty x p1.(1) => store_add_mul_rr_scale_x_y_z S1;
        ]

    (* store x (add y z) *)
    let store_add = [
      store `i8  x (add `i64 y z) => Sel.store_add;
      store `i16 x (add `i64 y z) => Sel.store_add;
      store `i32 x (add `i64 y z) => Sel.store_add;
      store `i64 x (add `i64 y z) => Sel.store_add;
      store `f32 x (add `i64 y z) => Sel.store_add;
      store `f64 x (add `i64 y z) => Sel.store_add;
    ]

    (* store x y *)
    let store_basic = [
      store `i8  x y => Sel.store;
      store `i16 x y => Sel.store;
      store `i32 x y => Sel.store;
      store `i64 x y => Sel.store;
      store `f32 x y => Sel.store;
      store `f64 x y => Sel.store;
    ]

    (* jmp x *)
    let jmp_basic = [
      jmp x => Sel.jmp;
    ]

    (* br ((x & y) == 0), yes, no
       br ((x & y) != 0), yes, no
       br (x == 0), yes, no
       br (x != 0), yes, no
    *)
    let br_zero = [
      `i8,  i8  0;
      `i16, i16 0;
      `i32, i32 0l;
      `i64, i64 0L;
    ] >* fun (ty, zero) ->
        let ty' = bty ty in [
          (* Test two operands. *)
          br (ne ty' (and_ ty x y) zero) yes no => Sel.br_test ();
          br (eq ty' (and_ ty x y) zero) yes no => Sel.br_test () ~neg:true;
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
          br (eq ty' x y) yes no => Sel.br_icmp Ce;
          br (ne ty' x y) yes no => Sel.br_icmp Cne;
          (* Unsigned *)
          br (lt ty' x y) yes no => Sel.br_icmp Cb;
          br (le ty' x y) yes no => Sel.br_icmp Cbe;
          br (gt ty' x y) yes no => Sel.br_icmp Ca;
          br (ge ty' x y) yes no => Sel.br_icmp Cae;
          (* Signed *)
          br (slt ty x y) yes no => Sel.br_icmp Cl;
          br (sle ty x y) yes no => Sel.br_icmp Cle;
          br (sgt ty x y) yes no => Sel.br_icmp Cg;
          br (sge ty x y) yes no => Sel.br_icmp Cge;
        ]

    let br_fcmp = [
      `f32, Sel.br_fcmp32;
      `f64, Sel.br_fcmp64;
    ] >* fun (ty, f) ->
        let ty' = bty ty in [
          (* Equality *)
          br (eq ty' x y) yes no => f Ce;
          br (ne ty' x y) yes no => f Cne;
          (* Comparison *)
          br (lt ty' x y) yes no => f Cb;
          br (le ty' x y) yes no => f Cbe;
          br (gt ty' x y) yes no => f Ca;
          br (ge ty' x y) yes no => f Cae;
          (* Ordering *)
          br (uo ty x y) yes no => f Cp;
          br (o ty x y) yes no => f Cnp;
        ]

    let br_bare = [
      br x yes no => jcc_r_zero_x ~neg:true;
    ]

    (* call x *)
    let call_basic = [
      call x y => Sel.call;
    ]

    (* tailcall x *)
    let tailcall_basic = [
      tailcall x y => Sel.tailcall;
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
      hlt => (fun _ -> !![I.ud2]);
    ]

    (* ret *)
    let ret = [
      ret => (fun _ -> !![I.ret]);
    ]
  end

  let rules =
    let open Rules in
    List.concat [
      add_mul_lea_imm;
      add_mul_lea_neg_imm;
      add_mul_lea;
      mul_lea_add_imm;
      add_basic;
      sub_basic;
      and_basic;
      or_basic;
      xor_basic;
      lsl_basic;
      lsr_basic;
      asr_basic;
      rol_basic;
      ror_basic;
      mul_basic;
      mulh_basic;
      umulh_basic;
      div_basic;
      rem_basic;
      udiv_basic;
      urem_basic;
      setcc_zero;
      setcc_ibasic;
      setcc_fbasic;
      sel_zero;
      sel_ibasic;
      sel_fbasic;
      sel_ifcmp;
      load_add_mul_disp;
      load_add_mul_disp_neg;
      load_add_mul;
      load_add;
      load_basic;
      neg_basic;
      not_basic;
      clz_basic;
      ctz_basic;
      popcnt_basic;
      bswap_basic;
      load_ext_add_mul_disp;
      load_ext_add_mul_disp_neg;
      load_ext_add_mul;
      load_ext_add;
      load_ext_basic;
      sext_basic;
      zext_basic;
      fext_basic;
      fibits_basic;
      ftosi_basic;
      ftoui_basic;
      ftrunc_basic;
      ifbits_basic;
      itrunc_basic;
      sitof_basic;
      flag_basic;
      move_basic;
      store_vec_add;
      store_vec_basic;
      store_add_mul_disp;
      store_add_mul_disp_neg;
      store_add_mul;
      store_add;
      store_basic;
      jmp_basic;
      br_zero;
      br_icmp;
      br_fcmp;
      br_bare;
      call_basic;
      tailcall_basic;
      sw_basic;
      hlt;
      ret;
    ]
end
