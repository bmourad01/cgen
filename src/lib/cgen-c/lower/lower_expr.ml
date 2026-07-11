open Core

module Bv = Cgen_utils.Bv
module IT = Cgen.Type
module Ctx = Cgen.Context
module S = Cgen.Structured
module V = Cgen.Virtual
module F32 = Cgen_utils.Float32
module LB = Layout.Bitfield
module Target = Cgen.Target
module Smap = Cgen_containers.Champ.Make(String)

type 'a map = 'a Smap.t

open Ctx.Syntax

let (let@) f x = f x

type env = {
  layout  : Layout.t;
  slots   : Cgen.Var.t map;
  strings : string String.Table.t;
  nstr    : int ref;
}

let dmodel env = Layout.dmodel env.layout
let ptr_imm env = Lower_type.pointer_imm (dmodel env)
let norm env ty = Type_env.normalize (Layout.tenv env.layout) ty
let fresh_var = Ctx.Var.fresh
let emit op rest : S.stmt = `seq (op, rest)

(* Allocate a stack slot for an object named `name` of type `ty`,
   optionally over-aligning the slot via `align`. *)
let alloc_slot ?align layout name ty =
  (* `Layout.sizeof`/`alignof` require a typedef-free type. *)
  let ty = Type_env.normalize (Layout.tenv layout) ty in
  let* v = Ctx.Var.fresh in
  let*? size = Layout.sizeof layout ty in
  let*? natural = Layout.alignof layout ty in
  let align = Option.value_map align ~default:natural ~f:(max natural) in
  let+? slot = V.Slot.create v ~size ~align in
  (name, v), slot

let is_imm : IT.basic -> bool = function
  | #IT.imm -> true
  | `f32 | `f64 -> false

let imm_of_basic (b : IT.basic) : IT.imm = match b with
  | #IT.imm as i -> i
  | `f32 | `f64 -> failwith "lower: expected an integer type"

let bv_of_int (i : IT.imm) (n : int) : Bv.t =
  let m = Bv.modulus (IT.sizeof_imm i) in
  Bv.(int n mod m)

let int_operand (i : IT.imm) (n : int) : V.operand = `int (bv_of_int i n, i)

let zero_operand : IT.basic -> V.operand = function
  | `f32 -> `float (F32.of_float 0.0)
  | `f64 -> `double 0.0
  | #IT.imm as i -> int_operand i 0

let scalar env ty = Lower_type.scalar env.layout ty
let scalar_basic env ty = fst (scalar env ty)
let scalar_imm env ty = imm_of_basic (scalar_basic env ty)

let intern_string env s : string =
  Hashtbl.find_or_add env.strings s ~default:(fun () ->
      let n = !(env.nstr) in
      incr env.nstr;
      Format.sprintf ".str%d" n)

(* {1 Operator mapping} *)

type bop_kind =
  | Arith of V.Insn.binop
  | Cmp of V.Insn.cmp

let bop_kind (op : Texpr.bop) (b : IT.basic) ~signed =
  let i () = imm_of_basic b in
  match op with
  | `add -> Arith (`add b)
  | `sub -> Arith (`sub b)
  | `mul -> Arith (`mul b)
  | `div -> if signed || not (is_imm b) then Arith (`div b) else Arith (`udiv (i ()))
  | `mod_ -> if signed then Arith (`rem (i ())) else Arith (`urem (i ()))
  | `and_ -> Arith (`and_ (i ()))
  | `or_ -> Arith (`or_ (i ()))
  | `xor -> Arith (`xor (i ()))
  | `shl -> Arith (`lsl_ (i ()))
  | `shr -> if signed then Arith (`asr_ (i ())) else Arith (`lsr_ (i ()))
  | `eq -> Cmp (`eq b)
  | `ne -> Cmp (`ne b)
  | `lt -> if signed && is_imm b then Cmp (`slt (i ())) else Cmp (`lt b)
  | `gt -> if signed && is_imm b then Cmp (`sgt (i ())) else Cmp (`gt b)
  | `le -> if signed && is_imm b then Cmp (`sle (i ())) else Cmp (`le b)
  | `ge -> if signed && is_imm b then Cmp (`sge (i ())) else Cmp (`ge b)

(* {1 Address arithmetic (pointer width)} *)

let add_offset env (base : V.operand) off k =
  if off = 0 then k base else
    let pi = ptr_imm env in
    let* x = fresh_var in
    let+ rest = k (`var x) in
    emit (`bop (x, `add (pi :> IT.basic), base, int_operand pi off)) rest

(* base + index * scale, in pointer width. *)
let add_scaled env (base : V.operand) (idx : V.operand) ~scale k =
  let pi = ptr_imm env in
  if scale = 1 then
    let* x = fresh_var in
    let+ rest = k (`var x) in
    emit (`bop (x, `add (pi :> IT.basic), base, idx)) rest
  else
    let* m = fresh_var in
    let* x = fresh_var in
    let+ rest = k (`var x) in
    S.Stmt.seq [
      `bop (m, `mul (pi :> IT.basic), idx, int_operand pi scale);
      `bop (x, `add (pi :> IT.basic), base, `var m);
      rest;
    ]

(* base - index * scale, in pointer width. *)
let sub_scaled env (base : V.operand) (idx : V.operand) ~scale k =
  let pi = ptr_imm env in
  if scale = 1 then
    let* x = fresh_var in
    let+ rest = k (`var x) in
    emit (`bop (x, `sub (pi :> IT.basic), base, idx)) rest
  else
    let* m = fresh_var in
    let* x = fresh_var in
    let+ rest = k (`var x) in
    S.Stmt.seq [
      `bop (m, `mul (pi :> IT.basic), idx, int_operand pi scale);
      `bop (x, `sub (pi :> IT.basic), base, `var m);
      rest;
    ]

(* The pointee (or array element) type of [ty], if it is a pointer or array;
   [None] for a scalar. Used to recognize pointer arithmetic. *)
let pointee_of env ty = match norm env ty with
  | Tptr {pointee; _} -> Some pointee
  | Tarray {elem; _} -> Some elem
  | _ -> None

(* {1 Bit fields} *)

let bv imm = Bv.modular (IT.sizeof_imm imm)

(* The placement of `parent_ty.field` if it is a bit field, else `None`. *)
let bitfield_info_opt env ~parent_ty ~field =
  match Lower_type.compound_tag env.layout parent_ty with
  | None -> None
  | Some tag -> Result.ok (Layout.bitfield_info env.layout ~tag ~field)

(* If `lv` is a member access naming a bit field, the parent (struct) lvalue
   and the field's placement; otherwise `None`. *)
let as_bitfield_lval env (lv : Texpr.tlval) = match lv.node with
  | Lmember {lval; field} ->
    Option.map (bitfield_info_opt env ~parent_ty:lval.ty ~field)
      ~f:(fun bf -> lval, bf)
  | _ -> None

(* The field's allocation offset within its run-time access integer. *)
let access_offset bf =
  LB.storage bf * 8 + LB.offset bf - LB.access_storage bf * 8

(* Whether the target orders bytes little-endian. *)
let little_endian = Ctx.target >>| Target.little

let access_lsb_offset ~little bf =
  let au = access_offset bf in
  if little then au else LB.access_bits bf - au - LB.width bf

(* The absolute bit position and covered byte span of a bit field, for the
   byte-wise access path. *)
let field_span bf =
  let p = LB.storage bf * 8 + LB.offset bf in
  let width = LB.width bf in
  p, width, p / 8, (p + width - 1) / 8

let bitfield_load_bytewise env ~base ~(bf : Layout.bitfield) ~ty k =
  let* little = little_endian in
  let b, signed = scalar env ty in
  let bi = imm_of_basic b in
  let pi = ptr_imm env in
  let p, width, byte_lo, byte_hi = field_span bf in
  let i64 : IT.imm = `i64 in
  let rec bytes byte acc pre =
    if byte > byte_hi then !!(acc, pre) else
      let* addr = fresh_var in
      let* raw = fresh_var in
      let* wide = fresh_var in
      let sh =
        if little then (byte - byte_lo) * 8 else (byte_hi - byte) * 8 in
      let this = [
        `bop (addr, `add (pi :> IT.basic), base, int_operand pi byte);
        `load (raw, (`i8 :> IT.arg), `var addr);
        `uop (wide, `zext i64, `var raw);
      ] in
      let* placed, this =
        if sh = 0 then !!(`var wide, this) else
          let+ s = fresh_var in
          let op = `bop (s, `lsl_ i64, `var wide, int_operand i64 sh) in
          `var s, this @ [op] in
      match acc with
      | None -> bytes (byte + 1) (Some placed) (pre @ this)
      | Some a ->
        let* n = fresh_var in
        bytes (byte + 1) (Some (`var n))
          (pre @ this @ [`bop (n, `or_ i64, a, placed)]) in
  let* acc, pre = bytes byte_lo None [] in
  let acc = Option.value_exn acc in
  let span = byte_hi - byte_lo + 1 in
  let foff = p - byte_lo * 8 in
  let lsb = if little then foff else span * 8 - foff - width in
  let* hi = fresh_var in
  let rsh : V.Insn.binop = if signed then `asr_ i64 else `lsr_ i64 in
  let* val64 = fresh_var in
  let* x, conv =
    if IT.equal_basic (`i64 :> IT.basic) b
    then !!(`var val64, [])
    else
      let+ x = fresh_var in
      `var x, [`uop (x, `itrunc bi, `var val64)] in
  let+ rest = k x in
  S.Stmt.seq @@ pre @ [
      `bop (hi, `lsl_ i64, acc, int_operand i64 (64 - lsb - width));
      `bop (val64, rsh, `var hi, int_operand i64 (64 - width));
    ] @ conv @ [rest]

let bitfield_store_bytewise env ~base ~(bf : Layout.bitfield)
    ~ty ~(value : V.operand) k =
  let* little = little_endian in
  let b, _ = scalar env ty in
  let bi = imm_of_basic b in
  let pi = ptr_imm env in
  let i8 : IT.imm = `i8 in
  let module A8 = (val bv i8) in
  let p, width, byte_lo, byte_hi = field_span bf in
  let rec bytes byte pre =
    if byte > byte_hi then !!pre else
      let lo = max p (byte * 8) and hi = min (p + width) (byte * 8 + 8) in
      let nbits = hi - lo in
      let src_shift =
        if little then lo - p else width - (hi - p) in
      let dst_shift =
        if little then lo - byte * 8 else 8 - (hi - byte * 8) in
      let* addr = fresh_var in
      let addr_i =
        `bop (addr, `add (pi :> IT.basic), base, int_operand pi byte) in
      let* sv, sv_is =
        if src_shift = 0 then !!(value, [])
        else let+ s = fresh_var in
          `var s, [`bop (s, `lsr_ bi, value, int_operand bi src_shift)] in
      let* v8, tr_is =
        if IT.equal_basic b (`i8 :> IT.basic) then !!(sv, [])
        else let+ v = fresh_var in `var v, [`uop (v, `itrunc i8, sv)] in
      if nbits >= 8 then
        bytes (byte + 1)
          (pre @ (addr_i :: sv_is) @ tr_is
           @ [`store ((`i8 :> IT.arg), v8, `var addr)])
      else
        let mask = A8.((pred (one lsl int nbits)) lsl int dst_shift) in
        let clear = A8.lnot mask in
        let* shifted, sh_is =
          if dst_shift = 0 then !!(v8, [])
          else let+ s = fresh_var in
            `var s, [`bop (s, `lsl_ i8, v8, int_operand i8 dst_shift)] in
        let* piece = fresh_var in
        let* raw = fresh_var in
        let* cleared = fresh_var in
        let* merged = fresh_var in
        bytes (byte + 1)
          (pre @ (addr_i :: sv_is) @ tr_is @ sh_is @ [
              `bop (piece, `and_ i8, shifted, `int (mask, i8));
              `load (raw, (`i8 :> IT.arg), `var addr);
              `bop (cleared, `and_ i8, `var raw, `int (clear, i8));
              `bop (merged, `or_ i8, `var cleared, `var piece);
              `store ((`i8 :> IT.arg), `var merged, `var addr);
            ]) in
  let* pre = bytes byte_lo [] in
  let+ rest = k () in
  S.Stmt.seq (pre @ [rest])

(* Read a bit field of type `ty`. *)
let bitfield_load env ~base ~(bf : Layout.bitfield) ~ty k =
  if LB.bytewise bf then bitfield_load_bytewise env ~base ~bf ~ty k else
    let@ addr = add_offset env base (LB.access_storage bf) in
    let* little = little_endian in
    let b, signed = scalar env ty in
    let bi = imm_of_basic b in
    let bits = IT.sizeof_imm bi in
    let width = LB.width bf in
    let aoff = access_lsb_offset ~little bf in
    let ab = (Lower_type.imm_of_bits (LB.access_bits bf) :> IT.basic) in
    let rsh : V.Insn.binop = if signed then `asr_ bi else `lsr_ bi in
    let* raw = fresh_var in
    let* wide, pre =
      if IT.equal_basic ab b then !!(`var raw, [])
      else let+ w = fresh_var in `var w, [`uop (w, `zext bi, `var raw)] in
    let* hi = fresh_var in
    let* x = fresh_var in
    let+ rest = k (`var x) in
    S.Stmt.seq @@
    `load (raw, (ab :> IT.arg), addr) :: pre @ [
      `bop (hi, `lsl_ bi, wide, int_operand bi (bits - aoff - width));
      `bop (x, rsh, `var hi, int_operand bi (bits - width));
      rest;
    ]

(* Write `value` into a bit field of type `ty`. *)
let bitfield_store env ~base ~bf ~ty ~(value : V.operand) k =
  if LB.bytewise bf then bitfield_store_bytewise env ~base ~bf ~ty ~value k else
    let@ addr = add_offset env base (LB.access_storage bf) in
    let* little = little_endian in
    let b, _ = scalar env ty in
    let width = LB.width bf in
    let aoff = access_lsb_offset ~little bf in
    let abi = Lower_type.imm_of_bits (LB.access_bits bf) in
    let ab = (abi :> IT.basic) in
    let module A = (val bv abi) in
    let field_mask = A.(pred (one lsl int width) lsl int aoff) in
    let clear_mask = A.lnot field_mask in
    let* vop, pre =
      if IT.equal_basic ab b then !!(value, [])
      else let+ v = fresh_var in `var v, [`uop (v, `itrunc abi, value)] in
    let* raw = fresh_var in
    let* cleared = fresh_var in
    let* shifted = fresh_var in
    let* bits = fresh_var in
    let* merged = fresh_var in
    let+ rest = k () in
    S.Stmt.seq @@ pre @ [
        `load (raw, (ab :> IT.arg), addr);
        `bop (cleared, `and_ abi, `var raw, `int (clear_mask, abi));
        `bop (shifted, `lsl_ abi, vop, int_operand abi aoff);
        `bop (bits, `and_ abi, `var shifted, `int (field_mask, abi));
        `bop (merged, `or_ abi, `var cleared, `var bits);
        `store ((ab :> IT.arg), `var merged, addr);
        rest;
      ]

(* {1 Expressions} *)

let rec lower_rval env (e : Texpr.t) k = match e.node with
  | Econst c -> lower_const env e.ty c k
  | Eenum_const {value; _} -> k (`int (value, scalar_imm env e.ty))
  | Efun name -> k (`sym (name, 0))
  | Evar _ ->
    let@ addr = lower_lval env (lval_of_rval e) in
    load_or_address env e.ty addr k
  | Emember {obj; field} ->
    lower_member env (lval_of_rval e) e.ty obj field k
  | Eindex {arr; idx} ->
    (* `arr` is the already-decayed base: a pointer value, or an array
       whose rvalue is its own address.

       Either way, `lower_rval` yields the base address, so compute the
       element address directly rather than rebuilding an lvalue (whose
       pointer case would deref again).
    *)
    let@ addr = index_addr env ~arr ~idx ~elem:e.ty in
    load_or_address env e.ty addr k
  | Eaddrof lv -> lower_lval env lv k
  | Eunary {op; arg} -> lower_unary env e op arg k
  | Ebinary {op; lhs; rhs} -> lower_binary env e op lhs rhs k
  | Ecast {dst; arg} -> lower_cast env ~dst arg k
  | Econd {cond; then_; else_} -> lower_cond env e cond then_ else_ k
  | Ecompound _ -> Ctx.failf "lower: compound literals are not yet supported" ()

and lower_member env lv ty (obj : Texpr.t) field k =
  match bitfield_info_opt env ~parent_ty:obj.ty ~field with
  | Some bf ->
    let@ base = lower_rval env obj in
    bitfield_load env ~base ~bf ~ty k
  | None ->
    let@ addr = lower_lval env lv in
    load_or_address env ty addr k

(* Rebuild the lvalue that an lvalue-valued rvalue accesses, so the
   address machinery is shared.

   An aggregate operand sub-expression already lowers to an address,
   so wrap it back as a dereference.
*)
and lval_of_rval (e : Texpr.t) : Texpr.tlval = match e.node with
  | Evar name ->
    {node = Lvar name; ty = e.ty}
  | Eindex {arr; idx} ->
    let d : Texpr.tlval = {node = Lderef arr; ty = arr.ty} in
    {node = Lindex {lval = d; index = idx}; ty = e.ty}
  | Emember {obj; field} ->
    let d : Texpr.tlval = {node = Lderef obj; ty = obj.ty} in
    {node = Lmember {lval = d; field}; ty = e.ty}
  | _ -> assert false

and lower_const env ty (c : Expr.const) k = match c with
  | Cint {value; _} -> k (`int (value, scalar_imm env ty))
  (* §6.4.4.4 ¶10: a character constant has type `int`; emit it at the
     expression's (promoted) width, not as a byte. *)
  | Cchar ch -> k (int_operand (scalar_imm env ty) (Char.to_int ch))
  | Cfloat f -> k (`float f)
  | Cdouble d -> k (`double d)
  | Cstr s -> k (`sym (intern_string env s, 0))

(* Load a scalar from `addr`, or, for an aggregate, pass `addr` through. *)
and load_or_address env ty (addr : V.operand) k =
  if Lower_type.is_aggregate env.layout ty then k addr else
    let b = scalar_basic env ty in
    let* x = fresh_var in
    let+ rest = k (`var x) in
    emit (`load (x, (b :> IT.arg), addr)) rest

and lower_unary env e (op : Texpr.uop) (arg : Texpr.t) k = match op with
  | `deref ->
    let@ p = lower_rval env arg in
    load_or_address env e.ty p k
  | `plus -> lower_rval env arg k
  | `minus ->
    let@ v = lower_rval env arg in
    let b = scalar_basic env arg.ty in
    let* x = fresh_var in
    let+ rest = k (`var x) in
    emit (`uop (x, `neg b, v)) rest
  | `not_ ->
    let@ v = lower_rval env arg in
    let i = scalar_imm env arg.ty in
    let* x = fresh_var in
    let+ rest = k (`var x) in
    emit (`uop (x, `not_ i, v)) rest
  | `lnot_ ->
    let@ v = lower_rval env arg in
    let b = scalar_basic env arg.ty in
    let ri = scalar_imm env e.ty in
    let* f = fresh_var in
    let* x = fresh_var in
    let+ rest = k (`var x) in
    S.Stmt.seq [
      `bop (f, `eq b, v, zero_operand b);
      `uop (x, `flag ri, `var f);
      rest;
    ]

and lower_binary env e (op : Texpr.bop) (lhs : Texpr.t) (rhs : Texpr.t) k =
  (* Pointer arithmetic (§6.5.6) needs the integer operand scaled by the
     pointee size and widened to pointer width.

     A pointer difference is the byte difference divided by the pointee size.
     Array subscripting reuses the same `add_scaled`/`lower_index` machinery.

     Everything else is scalar arithmetic whose operands already share a basic
     type after UAC.
  *)
  match op, pointee_of env lhs.ty, pointee_of env rhs.ty with
  | `add, Some pointee, None -> lower_ptr_int env `add ~ptr:lhs ~int_:rhs ~pointee k
  | `sub, Some pointee, None -> lower_ptr_int env `sub ~ptr:lhs ~int_:rhs ~pointee k
  | `add, None, Some pointee -> lower_ptr_int env `add ~ptr:rhs ~int_:lhs ~pointee k
  | `sub, Some pointee, Some _ -> lower_ptr_diff env ~lhs ~rhs ~pointee k
  | _ -> lower_scalar_binary env e op lhs rhs k

(* pointer +/- integer: the base is the pointer, the index is the integer
   widened to pointer width, scaled by the pointee size. *)
and lower_ptr_int env op ~ptr ~int_ ~pointee k =
  let@ base = lower_rval env ptr in
  let@ idx = lower_index env int_ in
  let*? scale = Layout.sizeof env.layout pointee in
  match op with
  | `add -> add_scaled env base idx ~scale k
  | `sub -> sub_scaled env base idx ~scale k

(* pointer - pointer: the byte difference divided by the pointee size, in
   (signed) ptrdiff_t, which is pointer width. *)
and lower_ptr_diff env ~lhs ~rhs ~pointee k =
  let@ l = lower_rval env lhs in
  let@ r = lower_rval env rhs in
  let pi = ptr_imm env in
  let*? scale = Layout.sizeof env.layout pointee in
  if scale = 1 then
    let* d = fresh_var in
    let+ rest = k (`var d) in
    emit (`bop (d, `sub (pi :> IT.basic), l, r)) rest
  else
    let* d = fresh_var in
    let* q = fresh_var in
    let+ rest = k (`var q) in
    S.Stmt.seq [
      `bop (d, `sub (pi :> IT.basic), l, r);
      `bop (q, `div (pi :> IT.basic), `var d, int_operand pi scale);
      rest;
    ]

and lower_scalar_binary env e (op : Texpr.bop) (lhs : Texpr.t) (rhs : Texpr.t) k =
  let@ l = lower_rval env lhs in
  let@ r = lower_rval env rhs in
  let b, signed = scalar env lhs.ty in
  match bop_kind op b ~signed with
  | Arith bop ->
    (* A shift count is integer-promoted independently of the value (§6.5.7).

       In C, it is allowed to be narrower, but the IR shift needs both at the
       value's width, so widen the count to match.
    *)
    let@ r = match op with
      | `shl | `shr ->
        let cb, csig = scalar env rhs.ty in
        if IT.sizeof_basic cb < IT.sizeof_basic b
        then lower_conv r ~sb:cb ~ssig:csig ~dst:b
        else (fun k -> k r)
      | _ -> (fun k -> k r) in
    let* x = fresh_var in
    let+ rest = k (`var x) in
    emit (`bop (x, bop, l, r)) rest
  | Cmp cmp ->
    let ri = scalar_imm env e.ty in
    let* f = fresh_var in
    let* x = fresh_var in
    let+ rest = k (`var x) in
    S.Stmt.seq [
      `bop (f, (cmp :> V.Insn.binop), l, r);
      `uop (x, `flag ri, `var f);
      rest;
    ]

and lower_cond env e cond then_ else_ k =
  let@ c = lower_rval env cond in
  let@ t = lower_rval env then_ in
  let@ el = lower_rval env else_ in
  let cb = scalar_basic env cond.ty in
  let rb = scalar_basic env e.ty in
  let* f = fresh_var in
  let* x = fresh_var in
  let+ rest = k (`var x) in
  S.Stmt.seq [
    `bop (f, `ne cb, c, zero_operand cb);
    `sel (x, rb, f, t, el);
    rest;
  ]

and lower_cast env ~(dst : Texpr.ty) (arg : Texpr.t) k =
  let@ v = lower_rval env arg in
  let agg t = Lower_type.is_aggregate env.layout t in
  if Type.is_void (norm env dst) then k v
  else if agg arg.ty then
    (* Array-to-pointer decay: an array rvalue already lowers to the
       address of its first element, which is the decayed pointer. *)
    k v
  else if agg dst then
    Ctx.failf "lower: casts to an aggregate type are not supported" ()
  else
    let sb, ssig = scalar env arg.ty in
    match norm env dst with
    | Tbase {base = Bbool; _} ->
      let* f = fresh_var in
      let* x = fresh_var in
      let+ rest = k (`var x) in
      S.Stmt.seq [
        `bop (f, `ne sb, v, zero_operand sb);
        `uop (x, `flag `i8, `var f);
        rest;
      ]
    | _ -> lower_conv v ~sb ~ssig ~dst:(scalar_basic env dst) k

(* Lower a conversion of basic types *)
and lower_conv (v : V.operand) ~sb ~ssig ~dst:db k =
  let conv u =
    let* x = fresh_var in
    let+ rest = k (`var x) in
    emit (`uop (x, u, v)) rest in
  match sb, db with
  (* Identity *)
  | _ when IT.equal_basic sb db -> k v
  (* Integer to integer *)
  | (#IT.imm as si), (#IT.imm as di) ->
    let sw = IT.sizeof_imm si and dw = IT.sizeof_imm di in
    (* Extension *)
    if dw > sw then conv (if ssig then `sext di else `zext di)
    (* Truncation *)
    else if dw < sw then conv (`itrunc di)
    else k v
  (* Integer to floating point *)
  | (#IT.imm as si), (#IT.fp as df) ->
    conv @@ if ssig
    then `sitof (si, df)
    else `uitof (si, df)
  (* Floating point to integer *)
  | (#IT.fp as sf), (#IT.imm as di) ->
    conv (`ftosi (sf, di))
  (* Floating point to floating point *)
  | (#IT.fp as sf), (#IT.fp as df) ->
    if IT.sizeof_fp df > IT.sizeof_fp sf
    then conv (`fext df)
    else conv (`ftrunc df)

(* {1 Lvalues (addresses)} *)

and lower_lval env (lv : Texpr.tlval) k = match lv.node with
  | Lvar name ->
    begin match Smap.find env.slots name with
      | Some slot -> k (`var slot)
      | None -> k (`sym (name, 0))
    end
  | Lderef e -> lower_rval env e k
  | Lmember {lval; field} ->
    let@ base = lower_lval env lval in
    let tag = Lower_type.compound_tag_exn env.layout lval.ty in
    let*? off = Layout.offsetof env.layout ~tag ~field in
    add_offset env base off k
  | Lindex {lval; index} ->
    let@ base = index_base env lval in
    let@ idx = lower_index env index in
    let*? scale = Layout.sizeof env.layout lv.ty in
    add_scaled env base idx ~scale k

and index_base env (lval : Texpr.tlval) k =
  match norm env lval.ty with
  | Tarray _ -> lower_lval env lval k
  | _ ->
    let@ addr = lower_lval env lval in
    let pi = ptr_imm env in
    let* x = fresh_var in
    let+ rest = k (`var x) in
    emit (`load (x, (pi :> IT.arg), addr)) rest

(* The address of `arr[idx]`, with `arr` the base-address rvalue. *)
and index_addr env ~arr ~(idx : Texpr.t) ~elem k =
  let@ base = lower_rval env arr in
  let@ i = lower_index env idx in
  let*? scale = Layout.sizeof env.layout elem in
  add_scaled env base i ~scale k

(* A subscript index in pointer width: extend the C index (signed or
   unsigned) to the pointer's integer type so the scaling arithmetic
   is well-typed. *)
and lower_index env (idx : Texpr.t) k =
  let@ v = lower_rval env idx in
  let sb, ssig = scalar env idx.ty in
  lower_conv v ~sb ~ssig ~dst:(ptr_imm env :> IT.basic) k

let rec lower_rvals env (es : Texpr.t list) k = match es with
  | [] -> k []
  | e :: rest ->
    let@ v = lower_rval env e in
    let@ vs = lower_rvals env rest in
    k (v :: vs)
