open Core
open Monads.Std

module O = Monad.Option
module I = Bv_interval

module Rules = struct
  module Subst = Egraph.Subst

  open Egraph.Rule
  open O.Let
  open O.Syntax

  let bv t = Bv.modular @@ Type.sizeof_imm t

  let is_const x env =
    Subst.find env x |>
    Option.bind ~f:Subst.const |>
    Option.is_some

  let is_not_const x env =
    Subst.find env x |>
    Option.bind ~f:Subst.const |>
    Option.is_none

  let is_neg_const x env =
    Option.is_some begin
      let* s = Subst.find env x in
      match Subst.const s with
      | Some `int (x, t) ->
        let module B = (val bv t) in
        O.guard @@ B.msb x
      | _ ->
        let* i = Subst.intv s in
        let n = I.create_negative ~size:(I.size i) in
        O.guard @@ I.contains n i
    end

  (* `x` is not 0 or 1 *)
  let is_not_bool x env =
    Option.value ~default:false begin
      let* s = Subst.find env x in
      match Subst.const s with
      | Some `int (i, _) -> !!Bv.(i <> one && i <> zero)
      | _ ->
        let+ i = Subst.intv s in
        not I.(contains_value i Bv.one || contains_value i Bv.zero)
    end

  let has_type x ty env =
    Subst.find env x |>
    Option.bind ~f:Subst.typ |> function
    | Some tx -> Type.equal tx ty
    | None -> false

  (* Edge case where lsr can subsume the result of an asr, which is when
     we are extracting the MSB. *)
  let lsr_asr_bitwidth a b env =
    Option.is_some begin
      let* a = Subst.find env a >>= Subst.const in
      let* b = Subst.find env b >>= Subst.const in
      match a, b with
      | `int (a, ty), `int (b, ty') when Type.equal_imm ty ty' ->
        let a = Bv.to_int64 a in
        let b = Bv.to_int64 b in
        let sz = Type.sizeof_imm ty - 1 in
        O.guard Int64.(a >= 0L && a <= b && b = of_int sz)
      | _ -> None
    end

  (* Dynamically rewrite a multiplication by a power of two into
     a left shift. *)
  let mul_imm_pow2 x y env =
    Subst.find env y >>= Subst.const >>= function
    | `int (i, ty) ->
      let i = Bv.to_int64 i in
      let+ () = O.guard Int64.(i <> 0L && (i land pred i) = 0L) in
      let module B = (val bv ty) in
      Op.(lsl_ ty x (int B.(int (Int64.ctz i)) ty))
    | _ -> None

  (* For a signed division by a power of two `n` modulo `k` bits, rewrite to:

     (x < 0 ? x + (y-1) : x) >>> n when x > 2

     ((x >> (k-1)) + x) >>> 1 otherwise
  *)
  let div_imm_pow2 x y env =
    Subst.find env y >>= Subst.const >>= function
    | `int (i, ty) ->
      let i = Bv.to_int64 i in
      let+ () = O.guard Int64.(
          i <> 0L &&
          i <> 1L &&
          (i land pred i) = 0L
        ) in
      let module B = (val bv ty) in
      let n = B.(int Int64.(ctz i)) in
      let i1 = B.(int64 Int64.(pred i)) in
      let s = B.(int (Type.sizeof_imm ty) - one) in
      let tb = (ty :> Type.basic) in
      if Int64.(i > 2L) then
        let cmp = Op.(slt ty x (int B.zero ty)) in
        Op.(asr_ ty (sel tb cmp (add tb x (int i1 ty)) x) (int n ty))
      else
        Op.(asr_ ty (add tb (lsr_ ty x (int s ty)) x) (int B.one ty))
    | _ -> None

  (* Turn a signed division/remainder by a constant non-power of two into
     a series of multiplications and shifts. *)
  let div_rem_imm_non_pow2 ?(rem = false) x y env =
    Subst.find env y >>= Subst.const >>= function
    | `int (i, ty) ->
      let n = Bv.to_int64 i in
      let+ () = O.guard Int64.(
          n <> -1L &&
          n <> 0L &&
          n <> 1L &&
          (n land pred n) <> 0L
        ) in
      let module B = (val bv ty) in
      let sz1 = Type.sizeof_imm ty - 1 in
      let s_mul, s_shr = Magic_div.signed i ty in
      let tb = (ty :> Type.basic) in
      let q1 = Op.(mulh ty x (int s_mul ty)) in
      let q2 =
        if Int64.(n > 0L) && B.msb s_mul then
          Op.add tb q1 x
        else if Int64.(n < 0L) && not (B.msb s_mul) then
          Op.sub tb q1 x
        else q1 in
      let q3 = if s_shr = 0 then q2
        else Op.(asr_ ty q2 (int B.(int s_shr) ty)) in
      let qf = Op.(add tb q3 (lsr_ ty q3 (int B.(int sz1) ty))) in
      if rem then Op.(sub tb x (mul tb qf (int i ty))) else qf
    | _ -> None

  (*  For a signed remainder by a power of two `n` modulo `k` bits, rewrite to:

      ((x + t) & (n-1)) - t

      where

      t = (x >>> (k-1)) >> (k - n)
  *)
  let rem_imm_pow2 x y env =
    Subst.find env y >>= Subst.const >>= function
    | `int (i, ty) ->
      let i' = Bv.to_int64 i in
      let+ () = O.guard Int64.(
          i' <> 0L &&
          i' <> 1L &&
          (i' land pred i') = 0L
        ) in
      let module B = (val bv ty) in
      let tb = (ty :> Type.basic) in
      let ss = B.(int (Type.sizeof_imm ty) - one) in
      let n = B.(int Int64.(ctz i')) in
      let su = B.(int (Type.sizeof_imm ty) - n) in
      let i1 = B.(i - one) in
      let t = Op.(lsr_ ty (asr_ ty x (int ss ty)) (int su ty)) in
      Op.(sub tb (and_ ty (add tb x t) (int i1 ty)) t)
    | _ -> None

  (* Dynamically rewrite an unsigned division by a power of two into
     a right shift. *)
  let udiv_imm_pow2 x y env =
    Subst.find env y >>= Subst.const >>= function
    | `int (i, ty) ->
      let i = Bv.to_int64 i in
      let+ () = O.guard Int64.(i <> 0L && (i land pred i) = 0L) in
      let module B = (val bv ty) in
      Op.(lsr_ ty x (int B.(int (Int64.ctz i)) ty))
    | _ -> None

  (* Dynamically rewrite an unsigned remainder by a power of two into
     a bitwise AND. *)
  let urem_imm_pow2 x y env =
    Subst.find env y >>= Subst.const >>= function
    | `int (i, ty) ->
      let i = Bv.to_int64 i in
      let i' = Int64.pred i in
      let+ () = O.guard Int64.(i <> 0L && (i land i') = 0L) in
      let module B = (val bv ty) in
      Op.(and_ ty x (int B.(int64 i') ty))
    | _ -> None

  (* Turn an unsigned division/remainder by a constant non-power of two
     into a series of multiplications and shifts. *)
  let udiv_urem_imm_non_pow2 ?(rem = false) x y env =
    Subst.find env y >>= Subst.const >>= function
    | `int (i, ty) ->
      let n = Bv.to_int64 i in
      let+ () = O.guard Int64.(
          n <> -1L &&
          n <> 0L &&
          n <> 1L &&
          (n land pred n) <> 0L
        ) in
      let module B = (val bv ty) in
      let u_mul, u_add, u_shr = Magic_div.unsigned i ty in
      let tb = (ty :> Type.basic) in
      let q1 = Op.(umulh ty x (int u_mul ty)) in
      let qf =
        if u_add then
          Op.(lsr_ ty
                (add tb (lsr_ ty (sub tb x q1) (int B.one ty)) q1)
                (int B.(int Int.(u_shr - 1)) ty))
        else if u_shr > 0 then
          Op.(lsr_ ty q1 (int B.(int u_shr) ty))
        else q1 in
      if not rem then qf
      else Op.(sub tb x (mul tb qf (int i ty)))
    | _ -> None

  (* Rewrite a multiplication by a constant that is not a power of two.

     Can be a series of shifts, additions, and subtractions. Essentially
     we are doing an algebraic factoring.
  *)
  let mul_imm_non_pow2 x y env =
    Subst.find env y >>= Subst.const >>= function
    | `int (i, ty) ->
      let n = Bv.to_int64 i in
      let n' = Int64.pred n in
      let+ () = O.guard Int64.(
          n <> -1L &&
          n <> 0L &&
          n <> 1L &&
          n land n' <> 0L
        ) in
      let module B = (val bv ty) in
      let tb = (ty :> Type.basic) in
      let n1 = Int64.succ n in
      if Int64.(n1 land n = 0L) then
        if Int64.(n = 3L) then
          (* Special case when n is 3, we bias towards the lower
             power of two. Shift-and-add addressing modes are common
             on several architectures. *)
          Op.(add tb (lsl_ ty x (int B.one ty)) x)
        else
          (* Next integer is a power of two, so shift up to it
             and then subtract x. *)
          let sh = Int64.ctz n1 in
          Op.(sub tb (lsl_ ty x (int B.(int sh) ty)) x)
      else if Int64.(n' land pred n' = 0L) then
        (* Previous integer is a power of two, so shift up to
           it and add x. *)
        let sh = Int64.ctz n' in
        Op.(add tb (lsl_ ty x (int B.(int sh) ty)) x)
      else
        (* Check the next and previous power of two, and see which
           one is closer. We'll add or subtract the remaining factor
           from the shift, which can be recursively rewritten. If we
           end up doing this too many times then it will outweigh the
           cost of just using a `mul` instruction. *)
        let z = Int64.floor_pow2 n in
        let z' = Int64.ceil_pow2 n in
        let d = Int64.(n - z) in
        let d' = Int64.(z' - n) in
        if Int64.(d <= d') then
          let sh = Int64.ctz z in
          Op.(add tb (lsl_ ty x (int B.(int sh) ty))
                (mul tb x (int B.(int64 d) ty)))
        else
          let sh = Int64.ctz z' in
          Op.(sub tb (lsl_ ty x (int B.(int sh) ty))
                (mul tb x (int B.(int64 d') ty)))
    | _ -> None

  let identity_same_type x ty env =
    let* tx = Subst.find env x >>= Subst.typ in
    let+ () = O.guard @@ Type.equal tx (ty :> Type.t) in
    var x

  let cannot_be_zero x env = Option.is_some begin
      let* s = Subst.find env x in
      match Subst.const s with
      | Some `int (i, _) -> O.guard @@ Bv.(i <> zero)
      | _ ->
        let* i = Subst.intv s in
        O.guard @@ not @@ I.contains_value i Bv.zero
    end

  let x = var "x"
  let y = var "y"
  let z = var "z"

  let is_const_x = is_const "x"
  let is_const_y = is_const "y"
  let is_not_const_y = is_not_const "y"
  let is_neg_const_y = is_neg_const "y"
  let is_not_bool_y = is_not_bool "y"
  let has_type_x = has_type "x"
  let lsr_asr_bitwidth_y_z = lsr_asr_bitwidth "y" "z"
  let mul_imm_pow2_y = mul_imm_pow2 x "y"
  let mul_imm_non_pow2_y = mul_imm_non_pow2 x "y"
  let div_imm_pow2_y = div_imm_pow2 x "y"
  let rem_imm_pow2_y = rem_imm_pow2 x "y"
  let div_imm_non_pow2_y = div_rem_imm_non_pow2 x "y"
  let rem_imm_non_pow2_y = div_rem_imm_non_pow2 x "y" ~rem:true
  let udiv_imm_pow2_y = udiv_imm_pow2 x "y"
  let urem_imm_pow2_y = urem_imm_pow2 x "y"
  let udiv_imm_non_pow2_y = udiv_urem_imm_non_pow2 x "y"
  let urem_imm_non_pow2_y = udiv_urem_imm_non_pow2 x "y" ~rem:true
  let identity_same_type_x = identity_same_type "x"
  let cannot_be_zero_x = cannot_be_zero "x"

  let rules = Egraph.create_table Op.[
      (* Commutativity of constants. *)
      (add `i8 x y =>? add `i8 y x) ~if_:is_const_x;
      (add `i16 x y =>? add `i16 y x) ~if_:is_const_x;
      (add `i32 x y =>? add `i32 y x) ~if_:is_const_x;
      (add `i64 x y =>? add `i64 y x) ~if_:is_const_x;
      (mul `i8 x y =>? mul `i8 y x) ~if_:is_const_x;
      (mul `i16 x y =>? mul `i16 y x) ~if_:is_const_x;
      (mul `i32 x y =>? mul `i32 y x) ~if_:is_const_x;
      (mul `i64 x y =>? mul `i64 y x) ~if_:is_const_x;
      (mulh `i8 x y =>? mulh `i8 y x) ~if_:is_const_x;
      (mulh `i16 x y =>? mulh `i16 y x) ~if_:is_const_x;
      (mulh `i32 x y =>? mulh `i32 y x) ~if_:is_const_x;
      (mulh `i64 x y =>? mulh `i64 y x) ~if_:is_const_x;
      (umulh `i8 x y =>? umulh `i8 y x) ~if_:is_const_x;
      (umulh `i16 x y =>? umulh `i16 y x) ~if_:is_const_x;
      (umulh `i32 x y =>? umulh `i32 y x) ~if_:is_const_x;
      (umulh `i64 x y =>? umulh `i64 y x) ~if_:is_const_x;
      (and_ `i8 x y =>? and_ `i8 y x) ~if_:is_const_x;
      (and_ `i16 x y =>? and_ `i16 y x) ~if_:is_const_x;
      (and_ `i32 x y =>? and_ `i32 y x) ~if_:is_const_x;
      (and_ `i64 x y =>? and_ `i64 y x) ~if_:is_const_x;
      (or_ `i8 x y =>? or_ `i8 y x) ~if_:is_const_x;
      (or_ `i16 x y =>? or_ `i16 y x) ~if_:is_const_x;
      (or_ `i32 x y =>? or_ `i32 y x) ~if_:is_const_x;
      (or_ `i64 x y =>? or_ `i64 y x) ~if_:is_const_x;
      (xor `i8 x y =>? xor `i8 y x) ~if_:is_const_x;
      (xor `i16 x y =>? xor `i16 y x) ~if_:is_const_x;
      (xor `i32 x y =>? xor `i32 y x) ~if_:is_const_x;
      (xor `i64 x y =>? xor `i64 y x) ~if_:is_const_x;
      (eq `i8 x y =>? eq `i8 y x) ~if_:is_const_x;
      (eq `i16 x y =>? eq `i16 y x) ~if_:is_const_x;
      (eq `i32 x y =>? eq `i32 y x) ~if_:is_const_x;
      (eq `i64 x y =>? eq `i64 y x) ~if_:is_const_x;
      (ne `i8 x y =>? ne `i8 y x) ~if_:is_const_x;
      (ne `i16 x y =>? ne `i16 y x) ~if_:is_const_x;
      (ne `i32 x y =>? ne `i32 y x) ~if_:is_const_x;
      (ne `i64 x y =>? ne `i64 y x) ~if_:is_const_x;
      (gt `i8 x y =>? lt `i8 y x) ~if_:is_const_x;
      (gt `i16 x y =>? lt `i16 y x) ~if_:is_const_x;
      (gt `i32 x y =>? lt `i32 y x) ~if_:is_const_x;
      (gt `i64 x y =>? lt `i64 y x) ~if_:is_const_x;
      (ge `i8 x y =>? le `i8 y x) ~if_:is_const_x;
      (ge `i16 x y =>? le `i16 y x) ~if_:is_const_x;
      (ge `i32 x y =>? le `i32 y x) ~if_:is_const_x;
      (ge `i64 x y =>? le `i64 y x) ~if_:is_const_x;
      (le `i8 x y =>? ge `i8 y x) ~if_:is_const_x;
      (le `i16 x y =>? ge `i16 y x) ~if_:is_const_x;
      (le `i32 x y =>? ge `i32 y x) ~if_:is_const_x;
      (le `i64 x y =>? ge `i64 y x) ~if_:is_const_x;
      (lt `i8 x y =>? gt `i8 y x) ~if_:is_const_x;
      (lt `i16 x y =>? gt `i16 y x) ~if_:is_const_x;
      (lt `i32 x y =>? gt `i32 y x) ~if_:is_const_x;
      (lt `i64 x y =>? gt `i64 y x) ~if_:is_const_x;
      (sgt `i8 x y =>? slt `i8 y x) ~if_:is_const_x;
      (sgt `i16 x y =>? slt `i16 y x) ~if_:is_const_x;
      (sgt `i32 x y =>? slt `i32 y x) ~if_:is_const_x;
      (sgt `i64 x y =>? slt `i64 y x) ~if_:is_const_x;
      (sge `i8 x y =>? sle `i8 y x) ~if_:is_const_x;
      (sge `i16 x y =>? sle `i16 y x) ~if_:is_const_x;
      (sge `i32 x y =>? sle `i32 y x) ~if_:is_const_x;
      (sge `i64 x y =>? sle `i64 y x) ~if_:is_const_x;
      (sle `i8 x y =>? sge `i8 y x) ~if_:is_const_x;
      (sle `i16 x y =>? sge `i16 y x) ~if_:is_const_x;
      (sle `i32 x y =>? sge `i32 y x) ~if_:is_const_x;
      (sle `i64 x y =>? sge `i64 y x) ~if_:is_const_x;
      (slt `i8 x y =>? sgt `i8 y x) ~if_:is_const_x;
      (slt `i16 x y =>? sgt `i16 y x) ~if_:is_const_x;
      (slt `i32 x y =>? sgt `i32 y x) ~if_:is_const_x;
      (slt `i64 x y =>? sgt `i64 y x) ~if_:is_const_x;
      (* Enable constant folding via associativity. *)
      (add `i8 (add `i8 x y) z =>? add `i8 x (add `i8 z y)) ~if_:is_const_y;
      (add `i16 (add `i16 x y) z =>? add `i16 x (add `i16 z y)) ~if_:is_const_y;
      (add `i32 (add `i32 x y) z =>? add `i32 x (add `i32 z y)) ~if_:is_const_y;
      (add `i64 (add `i64 x y) z =>? add `i64 x (add `i64 z y)) ~if_:is_const_y;
      (mul `i8 (mul `i8 x y) z =>? mul `i8 x (mul `i8 z y)) ~if_:is_const_y;
      (mul `i16 (mul `i16 x y) z =>? mul `i16 x (mul `i16 z y)) ~if_:is_const_y;
      (mul `i32 (mul `i32 x y) z =>? mul `i32 x (mul `i32 z y)) ~if_:is_const_y;
      (mul `i64 (mul `i64 x y) z =>? mul `i64 x (mul `i64 z y)) ~if_:is_const_y;
      (and_ `i8 (and_ `i8 x y) z =>? and_ `i8 x (and_ `i8 z y)) ~if_:is_const_y;
      (and_ `i16 (and_ `i16 x y) z =>? and_ `i16 x (and_ `i16 z y)) ~if_:is_const_y;
      (and_ `i32 (and_ `i32 x y) z =>? and_ `i32 x (and_ `i32 z y)) ~if_:is_const_y;
      (and_ `i64 (and_ `i64 x y) z =>? and_ `i64 x (and_ `i64 z y)) ~if_:is_const_y;
      (or_ `i8 (or_ `i8 x y) z =>? or_ `i8 x (or_ `i8 z y)) ~if_:is_const_y;
      (or_ `i16 (or_ `i16 x y) z =>? or_ `i16 x (or_ `i16 z y)) ~if_:is_const_y;
      (or_ `i32 (or_ `i32 x y) z =>? or_ `i32 x (or_ `i32 z y)) ~if_:is_const_y;
      (or_ `i64 (or_ `i64 x y) z =>? or_ `i64 x (or_ `i64 z y)) ~if_:is_const_y;
      (xor `i8 (xor `i8 x y) z =>? xor `i8 x (xor `i8 z y)) ~if_:is_const_y;
      (xor `i16 (xor `i16 x y) z =>? xor `i16 x (xor `i16 z y)) ~if_:is_const_y;
      (xor `i32 (xor `i32 x y) z =>? xor `i32 x (xor `i32 z y)) ~if_:is_const_y;
      (xor `i64 (xor `i64 x y) z =>? xor `i64 x (xor `i64 z y)) ~if_:is_const_y;
      (sub `i8 (sub `i8 x y) z =>? sub `i8 x (add `i8 z y)) ~if_:is_const_y;
      (sub `i16 (sub `i16 x y) z =>? sub `i16 x (add `i16 z y)) ~if_:is_const_y;
      (sub `i32 (sub `i32 x y) z =>? sub `i32 x (add `i32 z y)) ~if_:is_const_y;
      (sub `i64 (sub `i64 x y) z =>? sub `i64 x (add `i64 z y)) ~if_:is_const_y;
      (sub `i8 (sub `i8 x y) z =>? sub `i8 (sub `i8 x z) y) ~if_:is_const_x;
      (sub `i16 (sub `i16 x y) z =>? sub `i16 (sub `i16 x z) y) ~if_:is_const_x;
      (sub `i32 (sub `i32 x y) z =>? sub `i32 (sub `i32 x z) y) ~if_:is_const_x;
      (sub `i64 (sub `i64 x y) z =>? sub `i64 (sub `i64 x z) y) ~if_:is_const_x;
      (sub `i8 (add `i8 x y) z =>? sub `i8 x (sub `i8 z y)) ~if_:is_const_y;
      (sub `i16 (add `i16 x y) z =>? sub `i16 x (sub `i16 z y)) ~if_:is_const_y;
      (sub `i32 (add `i32 x y) z =>? sub `i32 x (sub `i32 z y)) ~if_:is_const_y;
      (sub `i64 (add `i64 x y) z =>? sub `i64 x (sub `i64 z y)) ~if_:is_const_y;
      (add `i8 (sub `i8 x y) z =>? add `i8 x (sub `i8 z y)) ~if_:is_const_y;
      (add `i16 (sub `i16 x y) z =>? add `i16 x (sub `i16 z y)) ~if_:is_const_y;
      (add `i32 (sub `i32 x y) z =>? add `i32 x (sub `i32 z y)) ~if_:is_const_y;
      (add `i64 (sub `i64 x y) z =>? add `i64 x (sub `i64 z y)) ~if_:is_const_y;
      (add `i8 (sub `i8 x y) z =>? sub `i8 (add `i8 x z) y) ~if_:is_const_x;
      (add `i16 (sub `i16 x y) z =>? sub `i16 (add `i16 x z) y) ~if_:is_const_x;
      (add `i32 (sub `i32 x y) z =>? sub `i32 (add `i32 x z) y) ~if_:is_const_x;
      (add `i64 (sub `i64 x y) z =>? sub `i64 (add `i64 x z) y) ~if_:is_const_x;
      (* x + (-y) = x - y when y is a constant *)
      (add `i8 x y =>? sub `i8 x (neg `i8 y)) ~if_:is_neg_const_y;
      (add `i16 x y =>? sub `i16 x (neg `i16 y)) ~if_:is_neg_const_y;
      (add `i32 x y =>? sub `i32 x (neg `i32 y)) ~if_:is_neg_const_y;
      (add `i64 x y =>? sub `i64 x (neg `i64 y)) ~if_:is_neg_const_y;
      (* x - (-y) = x + y when y is a constant *)
      (sub `i8 x y =>? add `i8 x (neg `i8 y)) ~if_:is_neg_const_y;
      (sub `i16 x y =>? add `i16 x (neg `i16 y)) ~if_:is_neg_const_y;
      (sub `i32 x y =>? add `i32 x (neg `i32 y)) ~if_:is_neg_const_y;
      (sub `i64 x y =>? add `i64 x (neg `i64 y)) ~if_:is_neg_const_y;
      (* x + (-y) = (-y) + x = x - y *)
      (add `i8 x (neg `i8 y) =>? sub `i8 x y) ~if_:is_not_const_y;
      (add `i16 x (neg `i16 y) =>? sub `i16 x y) ~if_:is_not_const_y;
      (add `i32 x (neg `i32 y) =>? sub `i32 x y) ~if_:is_not_const_y;
      (add `i64 x (neg `i64 y) =>? sub `i64 x y) ~if_:is_not_const_y;
      (add `i8 (neg `i8 y) x =>? sub `i8 x y) ~if_:is_not_const_y;
      (add `i16 (neg `i16 y) x =>? sub `i16 x y) ~if_:is_not_const_y;
      (add `i32 (neg `i32 y) x =>? sub `i32 x y) ~if_:is_not_const_y;
      (add `i64 (neg `i64 y) x =>? sub `i64 x y) ~if_:is_not_const_y;
      (* x - (-y) = x + y *)
      (sub `i8 x (neg `i8 y) =>? add `i8 x y) ~if_:is_not_const_y;
      (sub `i16 x (neg `i16 y) =>? add `i16 x y) ~if_:is_not_const_y;
      (sub `i32 x (neg `i32 y) =>? add `i32 x y) ~if_:is_not_const_y;
      (sub `i64 x (neg `i64 y) =>? add `i64 x y) ~if_:is_not_const_y;
      (* x + 0 = x. *)
      add `i8 x  (i8 0) => x;
      add `i16 x (i16 0) => x;
      add `i32 x (i32 0l) => x;
      add `i64 x (i64 0L) => x;
      (* x - 0 = x. *)
      sub `i8 x  (i8 0) => x;
      sub `i16 x (i16 0) => x;
      sub `i32 x (i32 0l) => x;
      sub `i64 x (i64 0L) => x;
      (* 0 - x = -x *)
      sub `i8  (i8 0) x => neg `i8 x;
      sub `i16 (i16 0) x => neg `i16 x;
      sub `i32 (i32 0l) x => neg `i32 x;
      sub `i64 (i64 0L) x => neg `i64 x;
      (* -(-x) = x *)
      neg `i8 (neg `i8 x) => x;
      neg `i16 (neg `i16 x) => x;
      neg `i32 (neg `i32 x) => x;
      neg `i64 (neg `i64 x) => x;
      (* ~(~x) = x *)
      not_ `i8 (not_ `i8 x) => x;
      not_ `i16 (not_ `i16 x) => x;
      not_ `i32 (not_ `i32 x) => x;
      not_ `i64 (not_ `i64 x) => x;
      (* ~x + 1 = -x *)
      add `i8 (not_ `i8 x) (i8 1) => neg `i8 x;
      add `i16 (not_ `i16 x) (i16 1) => neg `i16 x;
      add `i32 (not_ `i32 x) (i32 1l) => neg `i32 x;
      add `i64 (not_ `i64 x) (i64 1L) => neg `i64 x;
      (* -x * -y = x * y *)
      mul `i8 (neg `i8 x) (neg `i8 y) => mul `i8 x y;
      mul `i16 (neg `i16 x) (neg `i16 y) => mul `i16 x y;
      mul `i32 (neg `i32 x) (neg `i32 y) => mul `i32 x y;
      mul `i64 (neg `i64 x) (neg `i64 y) => mul `i64 x y;
      (* x - x = 0. *)
      sub `i8 x x =>  i8 0;
      sub `i16 x x => i16 0;
      sub `i32 x x => i32 0l;
      sub `i64 x x => i64 0L;
      (* x * 0 = 0. *)
      mul `i8 x  (i8 0) =>  i8 0;
      mul `i16 x (i16 0) => i16 0;
      mul `i32 x (i32 0l) => i32 0l;
      mul `i64 x (i64 0L) => i64 0L;
      mulh `i8 x  (i8 0) =>  i8 0;
      mulh `i16 x (i16 0) => i16 0;
      mulh `i32 x (i32 0l) => i32 0l;
      mulh `i64 x (i64 0L) => i64 0L;
      umulh `i8 x  (i8 0) =>  i8 0;
      umulh `i16 x (i16 0) => i16 0;
      umulh `i32 x (i32 0l) => i32 0l;
      umulh `i64 x (i64 0L) => i64 0L;
      (* x * 1 = x *)
      mul `i8 x  (i8 1) => x;
      mul `i16 x (i16 1) => x;
      mul `i32 x (i32 1l) => x;
      mul `i64 x (i64 1L) => x;
      mulh `i8 x  (i8 1) => x;
      mulh `i16 x (i16 1) => x;
      mulh `i32 x (i32 1l) => x;
      mulh `i64 x (i64 1L) => x;
      umulh `i8 x  (i8 1) => x;
      umulh `i16 x (i16 1) => x;
      umulh `i32 x (i32 1l) => x;
      umulh `i64 x (i64 1L) => x;
      (* x * -1 = -x *)
      mul `i8 x  (i8 (-1)) => neg `i8 x;
      mul `i16 x (i16 (-1)) => neg `i16 x;
      mul `i32 x (i32 (-1l)) => neg `i32 x;
      mul `i64 x (i64 (-1L)) => neg `i64 x;
      (* x * 2 = x + x *)
      mul `i8  x (i8 2) => add `i8 x x;
      mul `i16 x (i16 2) => add `i16 x x;
      mul `i32 x (i32 2l) => add `i32 x x;
      mul `i64  x(i64 2L) => add `i64 x x;
      (* x * c = x << log2(c) when c is a constant *)
      mul `i8 x y =>* mul_imm_pow2_y;
      mul `i16 x y =>* mul_imm_pow2_y;
      mul `i32 x y =>* mul_imm_pow2_y;
      mul `i64 x y =>* mul_imm_pow2_y;
      mul `i8 x y =>* mul_imm_non_pow2_y;
      mul `i16 x y =>* mul_imm_non_pow2_y;
      mul `i32 x y =>* mul_imm_non_pow2_y;
      mul `i64 x y =>* mul_imm_non_pow2_y;
      (* signed x / c when c is constant *)
      div `i8 x y =>* div_imm_pow2_y;
      div `i16 x y =>* div_imm_pow2_y;
      div `i32 x y =>* div_imm_pow2_y;
      div `i64 x y =>* div_imm_pow2_y;
      div `i8 x y =>* div_imm_non_pow2_y;
      div `i16 x y =>* div_imm_non_pow2_y;
      div `i32 x y =>* div_imm_non_pow2_y;
      div `i64 x y =>* div_imm_non_pow2_y;
      (* signed x % c when c is a constant *)
      rem `i8 x y =>* rem_imm_pow2_y;
      rem `i16 x y =>* rem_imm_pow2_y;
      rem `i32 x y =>* rem_imm_pow2_y;
      rem `i64 x y =>* rem_imm_pow2_y;
      rem `i8 x y =>* rem_imm_non_pow2_y;
      rem `i16 x y =>* rem_imm_non_pow2_y;
      rem `i32 x y =>* rem_imm_non_pow2_y;
      rem `i64 x y =>* rem_imm_non_pow2_y;
      (* unsigned x / c = x >> log2(c) when c is a constant *)
      udiv `i8 x y =>* udiv_imm_pow2_y;
      udiv `i16 x y =>* udiv_imm_pow2_y;
      udiv `i32 x y =>* udiv_imm_pow2_y;
      udiv `i64 x y =>* udiv_imm_pow2_y;
      udiv `i8 x y =>* udiv_imm_non_pow2_y;
      udiv `i16 x y =>* udiv_imm_non_pow2_y;
      udiv `i32 x y =>* udiv_imm_non_pow2_y;
      udiv `i64 x y =>* udiv_imm_non_pow2_y;
      (* unsigned x % c = x & (c - 1) when c is a constant *)
      urem `i8 x y =>* urem_imm_pow2_y;
      urem `i16 x y =>* urem_imm_pow2_y;
      urem `i32 x y =>* urem_imm_pow2_y;
      urem `i64 x y =>* urem_imm_pow2_y;
      urem `i8 x y =>* urem_imm_non_pow2_y;
      urem `i16 x y =>* urem_imm_non_pow2_y;
      urem `i32 x y =>* urem_imm_non_pow2_y;
      urem `i64 x y =>* urem_imm_non_pow2_y;
      (* x / 1 = x *)
      div `i8  x (i8 1) => x;
      div `i16 x (i16 1) => x;
      div `i32 x (i32 1l) => x;
      div `i64 x (i64 1L) => x;
      udiv `i8 x (i8 1) => x;
      udiv `i16 x (i16 1) => x;
      udiv `i32 x (i32 1l) => x;
      udiv `i64 x (i64 1L) => x;
      (* x / x = 1 when x cannot be zero *)
      (div `i8 x x =>? i8 1) ~if_:cannot_be_zero_x;
      (div `i16 x x =>? i16 1) ~if_:cannot_be_zero_x;
      (div `i32 x x =>? i32 1l) ~if_:cannot_be_zero_x;
      (div `i64 x x =>? i64 1L) ~if_:cannot_be_zero_x;
      (udiv `i8 x x =>? i8 1) ~if_:cannot_be_zero_x;
      (udiv `i16 x x =>? i16 1) ~if_:cannot_be_zero_x;
      (udiv `i32 x x =>? i32 1l) ~if_:cannot_be_zero_x;
      (udiv `i64 x x =>? i64 1L) ~if_:cannot_be_zero_x;
      (* signed x / -1 = -x *)
      div `i8 x (i8 (-1)) => neg `i8 x;
      div `i16 x (i16 (-1)) => neg `i16 x;
      div `i32 x (i32 (-1l)) => neg `i32 x;
      div `i64 x (i64 (-1L)) => neg `i64 x;
      (* unsigned x / -1 = x == -1 *)
      udiv `i8 x (i8 (-1)) => flag `i8 (eq `i8 x (i8 (-1)));
      udiv `i16 x (i16 (-1)) => flag `i16 (eq `i16 x (i16 (-1)));
      udiv `i32 x (i32 (-1l)) => flag `i32 (eq `i32 x (i32 (-1l)));
      udiv `i64 x (i64 (-1L)) => flag `i64 (eq `i64 x (i64 (-1L)));
      (* x % 1 = 0 *)
      rem `i8 x (i8 1) => i8 0;
      rem `i16 x (i16 1) => i16 0;
      rem `i32 x (i32 1l) => i32 0l;
      rem `i64 x (i64 1L) => i64 0L;
      urem `i8 x (i8 1) => i8 0;
      urem `i16 x (i16 1) => i16 0;
      urem `i32 x (i32 1l) => i32 0l;
      urem `i64 x (i64 1L) => i64 0L;
      (* x % x = 0 when x cannot be zero *)
      (rem `i8 x x =>? i8 0) ~if_:cannot_be_zero_x;
      (rem `i16 x x =>? i16 0) ~if_:cannot_be_zero_x;
      (rem `i32 x x =>? i32 0l) ~if_:cannot_be_zero_x;
      (rem `i64 x x =>? i64 0L) ~if_:cannot_be_zero_x;
      (urem `i8 x x =>? i8 0) ~if_:cannot_be_zero_x;
      (urem `i16 x x =>? i16 0) ~if_:cannot_be_zero_x;
      (urem `i32 x x =>? i32 0l) ~if_:cannot_be_zero_x;
      (urem `i64 x x =>? i64 0L) ~if_:cannot_be_zero_x;
      (* signed x % -1 = 0 *)
      rem `i8 x (i8 (-1)) => i8 0;
      rem `i16 x (i16 (-1)) => i16 0;
      rem `i32 x (i32 (-1l)) => i32 0l;
      rem `i64 x (i64 (-1L)) => i64 0L;
      (* unsigned x % -1 = x != -1 *)
      urem `i8 x (i8 (-1)) => flag `i8 (ne `i8 x (i8 (-1)));
      urem `i16 x (i16 (-1)) => flag `i16 (ne `i16 x (i16 (-1)));
      urem `i32 x (i32 (-1l)) => flag `i32 (ne `i32 x (i32 (-1l)));
      urem `i64 x (i64 (-1L)) => flag `i64 (ne `i64 x (i64 (-1L)));
      (* x & 0 = 0 *)
      and_ `i8 x (i8 0) => i8 0;
      and_ `i16 x (i16 0) => i16 0;
      and_ `i32 x (i32 0l) => i32 0l;
      and_ `i64 x (i64 0L) => i64 0L;
      (* x & 0xff... = x *)
      and_ `i8 x  (i8 0xff) => x;
      and_ `i16 x (i16 0xffff) => x;
      and_ `i32 x (i32 0xffff_ffffl) => x;
      and_ `i64 x (i64 0xffff_ffff_ffff_ffffL) => x;
      (* x & x = x *)
      and_ `i8 x x => x;
      and_ `i16 x x => x;
      and_ `i32 x x => x;
      and_ `i64 x x => x;
      (* x | 0 = x *)
      or_ `i8 x (i8 0) => x;
      or_ `i16 x (i16 0) => x;
      or_ `i32 x (i32 0l) => x;
      or_ `i64 x (i64 0L) => x;
      (* x | 0xff... = 0xff... *)
      or_ `i8 x (i8 0xff) => i8 0xff;
      or_ `i16 x (i16 0xffff) => i16 0xffff;
      or_ `i32 x (i32 0xffff_ffffl) => i32 0xffff_ffffl;
      or_ `i64 x (i64 0xffff_ffff_ffff_ffffL) => i64 0xffff_ffff_ffff_ffffL;
      (* x | x = x *)
      or_ `i8 x x => x;
      or_ `i16 x x => x;
      or_ `i32 x x => x;
      or_ `i64 x x => x;
      (* x | ~x = 0xff... *)
      or_ `i8 x (not_ `i8 x) => i8 0xff;
      or_ `i16 x (not_ `i16 x) => i16 0xffff;
      or_ `i32 x (not_ `i32 x) => i32 0xffff_ffffl;
      or_ `i64 x (not_ `i64 x) => i64 0xffff_ffff_ffff_ffffL;
      (* ~x | x = 0xff... *)
      or_ `i8 (not_ `i8 x) x => i8 0xff;
      or_ `i16 (not_ `i16 x) x => i16 0xffff;
      or_ `i32 (not_ `i32 x) x => i32 0xffff_ffffl;
      or_ `i64 (not_ `i64 x) x => i64 0xffff_ffff_ffff_ffffL;
      (* ~(x | y) = ~x & ~y *)
      not_ `i8 (or_ `i8 x y) => and_ `i8 (not_ `i8 x) (not_ `i8 y);
      not_ `i16 (or_ `i16 x y) => and_ `i16 (not_ `i16 x) (not_ `i16 y);
      not_ `i32 (or_ `i32 x y) => and_ `i32 (not_ `i32 x) (not_ `i32 y);
      not_ `i64 (or_ `i64 x y) => and_ `i64 (not_ `i64 x) (not_ `i64 y);
      (* ~(x & y) = ~x | ~y *)
      not_ `i8 (and_ `i8 x y) => or_ `i8 (not_ `i8 x) (not_ `i8 y);
      not_ `i16 (and_ `i16 x y) => or_ `i16 (not_ `i16 x) (not_ `i16 y);
      not_ `i32 (and_ `i32 x y) => or_ `i32 (not_ `i32 x) (not_ `i32 y);
      not_ `i64 (and_ `i64 x y) => or_ `i64 (not_ `i64 x) (not_ `i64 y);
      (* (x & y) | ~y = x | ~y *)
      or_ `i8 (and_ `i8 x y) (not_ `i8 y) => or_ `i8 x (not_ `i8 y);
      or_ `i16 (and_ `i16 x y) (not_ `i16 y) => or_ `i16 x (not_ `i16 y);
      or_ `i32 (and_ `i32 x y) (not_ `i32 y) => or_ `i32 x (not_ `i32 y);
      or_ `i64 (and_ `i64 x y) (not_ `i64 y) => or_ `i64 x (not_ `i64 y);
      (* ~y | (x & y) => x | ~y *)
      or_ `i8 (not_ `i8 y) (and_ `i8 x y) => or_ `i8 x (not_ `i8 y);
      or_ `i16 (not_ `i16 y) (and_ `i16 x y) => or_ `i16 x (not_ `i16 y);
      or_ `i32 (not_ `i32 y) (and_ `i32 x y) => or_ `i32 x (not_ `i32 y);
      or_ `i64 (not_ `i64 y) (and_ `i64 x y) => or_ `i64 x (not_ `i64 y);
      (* x >>> 0 = x *)
      asr_ `i8 x (i8 0) => x;
      asr_ `i16 x (i16 0) => x;
      asr_ `i32 x (i32 0l) => x;
      asr_ `i64 x (i64 0L) => x;
      (* x << 0 = x *)
      lsl_ `i8 x (i8 0) => x;
      lsl_ `i16 x (i16 0) => x;
      lsl_ `i32 x (i32 0l) => x;
      lsl_ `i64 x (i64 0L) => x;
      (* x >> 0 = x *)
      lsr_ `i8 x (i8 0) => x;
      lsr_ `i16 x (i16 0) => x;
      lsr_ `i32 x (i32 0l) => x;
      lsr_ `i64 x (i64 0L) => x;
      (* (x >>> y) >> z = x >> z when z >= y and z is bitwidth - 1 *)
      (lsr_ `i8 (asr_ `i8 x y) z =>? (lsr_ `i8 x z)) ~if_:lsr_asr_bitwidth_y_z;
      (lsr_ `i16 (asr_ `i16 x y) z =>? (lsr_ `i16 x z)) ~if_:lsr_asr_bitwidth_y_z;
      (lsr_ `i32 (asr_ `i32 x y) z =>? (lsr_ `i32 x z)) ~if_:lsr_asr_bitwidth_y_z;
      (lsr_ `i64 (asr_ `i64 x y) z =>? (lsr_ `i64 x z)) ~if_:lsr_asr_bitwidth_y_z;
      (* rol x 0 = x *)
      rol `i8 x (i8 0) => x;
      rol `i16 x (i16 0) => x;
      rol `i32 x (i32 0l) => x;
      rol `i64 x (i64 0L) => x;
      (* ror x 0 = x *)
      ror `i8 x (i8 0) => x;
      ror `i16 x (i16 0) => x;
      ror `i32 x (i32 0l) => x;
      ror `i64 x (i64 0L) => x;
      (* x ^ 0 = x *)
      xor `i8 x (i8 0) => x;
      xor `i16 x (i16 0) => x;
      xor `i32 x (i32 0l) => x;
      xor `i64 x (i64 0L) => x;
      (* x ^ 0xff... = ~x *)
      xor `i8 x (i8 0xff) => not_ `i8 x;
      xor `i16 x (i16 0xffff) => not_ `i16 x;
      xor `i32 x (i32 0xffff_ffffl) => not_ `i32 x;
      xor `i64 x (i64 0xffff_ffff_ffff_ffffL) => not_ `i64 x;
      (* x ^ x = 0 *)
      xor `i8 x x => i8 0;
      xor `i16 x x => i16 0;
      xor `i32 x x => i32 0l;
      xor `i64 x x => i64 0L;
      (* x ^ ~x = 0xff... *)
      xor `i8 x (not_ `i8 x) => i8 0xff;
      xor `i16 x (not_ `i16 x) => i16 0xffff;
      xor `i32 x (not_ `i32 x) => i32 0xffff_ffffl;
      xor `i64 x (not_ `i64 x) => i64 0xffff_ffff_ffff_ffffL;
      (* ~x ^ x = 0xff... *)
      xor `i8 (not_ `i8 x) x => i8 0xff;
      xor `i16 (not_ `i16 x) x => i16 0xffff;
      xor `i32 (not_ `i32 x) x => i32 0xffff_ffffl;
      xor `i64 (not_ `i64 x) x => i64 0xffff_ffff_ffff_ffffL;
      (* (x ^ y) ^ y = x *)
      xor `i8 (xor `i8 x y) y => x;
      xor `i16 (xor `i16 x y) y => x;
      xor `i32 (xor `i32 x y) y => x;
      xor `i64 (xor `i64 x y) y => x;
      (* (y ^ x) ^ y = x *)
      xor `i8 (xor `i8 y x) y => x;
      xor `i16 (xor `i16 y x) y => x;
      xor `i32 (xor `i32 y x) y => x;
      xor `i64 (xor `i64 y x) y => x;
      (* y ^ (x ^ y) = x *)
      xor `i8 y (xor `i8 x y) => x;
      xor `i16 y (xor `i16 x y) => x;
      xor `i32 y (xor `i32 x y) => x;
      xor `i64 y (xor `i64 x y) => x;
      (* y ^ (y ^ x) = x *)
      xor `i8 y (xor `i8 y x) => x;
      xor `i16 y (xor `i16 y x) => x;
      xor `i32 y (xor `i32 y x) => x;
      xor `i64 y (xor `i64 y x) => x;
      (* x == x = true *)
      eq `i8 x x => bool true;
      eq `i16 x x => bool true;
      eq `i32 x x => bool true;
      eq `i64 x x => bool true;
      (* x != x = false *)
      ne `i8 x x => bool false;
      ne `i16 x x => bool false;
      ne `i32 x x => bool false;
      ne `i64 x x => bool false;
      (* x >= x = true *)
      ge `i8 x x => bool true;
      ge `i16 x x => bool true;
      ge `i32 x x => bool true;
      ge `i64 x x => bool true;
      sge `i8 x x => bool true;
      sge `i16 x x => bool true;
      sge `i32 x x => bool true;
      sge `i64 x x => bool true;
      (* x > x = false *)
      gt `i8 x x => bool false;
      gt `i16 x x => bool false;
      gt `i32 x x => bool false;
      gt `i64 x x => bool false;
      sgt `i8 x x => bool false;
      sgt `i16 x x => bool false;
      sgt `i32 x x => bool false;
      sgt `i64 x x => bool false;
      (* x <= x = true *)
      le `i8 x x => bool true;
      le `i16 x x => bool true;
      le `i32 x x => bool true;
      le `i64 x x => bool true;
      sle `i8 x x => bool true;
      sle `i16 x x => bool true;
      sle `i32 x x => bool true;
      sle `i64 x x => bool true;
      (* x < x = false *)
      lt `i8 x x => bool false;
      lt `i16 x x => bool false;
      lt `i32 x x => bool false;
      lt `i64 x x => bool false;
      slt `i8 x x => bool false;
      slt `i16 x x => bool false;
      slt `i32 x x => bool false;
      slt `i64 x x => bool false;
      (* flag (x == y) ^ 1 => flag (x != y) *)
      xor `i8 (flag `i8 (eq `i8 x y)) (i8 1) => flag `i8 (ne `i8 x y);
      xor `i16 (flag `i16 (eq `i16 x y)) (i16 1) => flag `i16 (ne `i16 x y);
      xor `i32 (flag `i32 (eq `i32 x y)) (i32 1l) => flag `i32 (ne `i32 x y);
      xor `i64 (flag `i64 (eq `i64 x y)) (i64 1L) => flag `i64 (ne `i64 x y);
      (* flag (x != y) ^ 1 => x == y *)
      xor `i8 (flag `i8 (ne `i8 x y)) (i8 1) => flag `i8 (eq `i8 x y);
      xor `i16 (flag `i16 (ne `i16 x y)) (i16 1) => flag `i16 (eq `i16 x y);
      xor `i32 (flag `i32 (ne `i32 x y)) (i32 1l) => flag `i32 (eq `i32 x y);
      xor `i64 (flag `i64 (ne `i64 x y)) (i64 1L) => flag `i64 (eq `i64 x y);
      (* flag (x >= y) ^ 1 => x < y *)
      xor `i8 (flag `i8 (ge `i8 x y)) (i8 1) => flag `i8 (lt `i8 x y);
      xor `i16 (flag `i16 (ge `i16 x y)) (i16 1) => flag `i16 (lt `i16 x y);
      xor `i32 (flag `i32 (ge `i32 x y)) (i32 1l) => flag `i32 (lt `i32 x y);
      xor `i64 (flag `i64 (ge `i64 x y)) (i64 1L) => flag `i64 (lt `i64 x y);
      xor `i8 (flag `i8 (sge `i8 x y)) (i8 1) => flag `i8 (slt `i8 x y);
      xor `i16 (flag `i16 (sge `i16 x y)) (i16 1) => flag `i16 (slt `i16 x y);
      xor `i32 (flag `i32 (sge `i32 x y)) (i32 1l) => flag `i32 (slt `i32 x y);
      xor `i64 (flag `i64 (sge `i64 x y)) (i64 1L) => flag `i64 (slt `i64 x y);
      (* flag (x > y) ^ 1 => x <= y *)
      xor `i8 (flag `i8 (gt `i8 x y)) (i8 1) => flag `i8 (le `i8 x y);
      xor `i16 (flag `i16 (gt `i16 x y)) (i16 1) => flag `i16 (le `i16 x y);
      xor `i32 (flag `i32 (gt `i32 x y)) (i32 1l) => flag `i32 (le `i32 x y);
      xor `i64 (flag `i64 (gt `i64 x y)) (i64 1L) => flag `i64 (le `i64 x y);
      xor `i8 (flag `i8 (sgt `i8 x y)) (i8 1) => flag `i8 (sle `i8 x y);
      xor `i16 (flag `i16 (sgt `i16 x y)) (i16 1) => flag `i16 (sle `i16 x y);
      xor `i32 (flag `i32 (sgt `i32 x y)) (i32 1l) => flag `i32 (sle `i32 x y);
      xor `i64 (flag `i64 (sgt `i64 x y)) (i64 1L) => flag `i64 (sle `i64 x y);
      (* flag (x <= y) ^ 1 => x > y *)
      xor `i8 (flag `i8 (le `i8 x y)) (i8 1) => flag `i8 (gt `i8 x y);
      xor `i16 (flag `i16 (le `i16 x y)) (i16 1) => flag `i16 (gt `i16 x y);
      xor `i32 (flag `i32 (le `i32 x y)) (i32 1l) => flag `i32 (gt `i32 x y);
      xor `i64 (flag `i64 (le `i64 x y)) (i64 1L) => flag `i64 (gt `i64 x y);
      xor `i8 (flag `i8 (sle `i8 x y)) (i8 1) => flag `i8 (sgt `i8 x y);
      xor `i16 (flag `i16 (sle `i16 x y)) (i16 1) => flag `i16 (sgt `i16 x y);
      xor `i32 (flag `i32 (sle `i32 x y)) (i32 1l) => flag `i32 (sgt `i32 x y);
      xor `i64 (flag `i64 (sle `i64 x y)) (i64 1L) => flag `i64 (sgt `i64 x y);
      (* flag (x < y) ^ 1 => x >= y *)
      xor `i8 (flag `i8 (lt `i8 x y)) (i8 1) => flag `i8 (ge `i8 x y);
      xor `i16 (flag `i16 (lt `i16 x y)) (i16 1) => flag `i16 (ge `i16 x y);
      xor `i32 (flag `i32 (lt `i32 x y)) (i32 1l) => flag `i32 (ge `i32 x y);
      xor `i64 (flag `i64 (lt `i64 x y)) (i64 1L) => flag `i64 (ge `i64 x y);
      xor `i8 (flag `i8 (slt `i8 x y)) (i8 1) => flag `i8 (sge `i8 x y);
      xor `i16 (flag `i16 (slt `i16 x y)) (i16 1) => flag `i16 (sge `i16 x y);
      xor `i32 (flag `i32 (slt `i32 x y)) (i32 1l) => flag `i32 (sge `i32 x y);
      xor `i64 (flag `i64 (slt `i64 x y)) (i64 1L) => flag `i64 (sge `i64 x y);
      (* unsigned x < 0 = false *)
      lt `i8 x (i8 0) => bool false;
      lt `i16 x (i16 0) => bool false;
      lt `i32 x (i32 0l) => bool false;
      lt `i64 x (i64 0L) => bool false;
      (* unsigned x >= 0 = true *)
      ge `i8 x (i8 0) => bool true;
      ge `i16 x (i16 0) => bool true;
      ge `i32 x (i32 0l) => bool true;
      ge `i64 x (i64 0L) => bool true;
      (* unsigned x <= 0 = x == 0 *)
      le `i8 x (i8 0) => eq `i8 x (i8 0);
      le `i16 x (i16 0) => eq `i16 x (i16 0);
      le `i32 x (i32 0l) => eq `i32 x (i32 0l);
      le `i64 x (i64 0L) => eq `i64 x (i64 0L);
      (* unsigned x > 0 = x != 0 *)
      gt `i8 x (i8 0) => ne `i8 x (i8 0);
      gt `i16 x (i16 0) => ne `i16 x (i16 0);
      gt `i32 x (i32 0l) => ne `i32 x (i32 0l);
      gt `i64 x (i64 0L) => ne `i64 x (i64 0L);
      (* unsigned x < 0xff... = x != 0xff... *)
      lt `i8 x (i8 0xff) => ne `i8 x (i8 0xff);
      lt `i16 x (i16 0xffff) => ne `i16 x (i16 0xffff);
      lt `i32 x (i32 0xffff_ffffl) => ne `i32 x (i32 0xffff_ffffl);
      lt `i64 x (i64 0xffff_ffff_ffff_ffffL) => ne `i64 x (i64 0xffff_ffff_ffff_ffffL);
      (* unsigned x <= 0xff... = true *)
      le `i8 x (i8 0xff) => bool true;
      le `i16 x (i16 0xffff) => bool true;
      le `i32 x (i32 0xffff_ffffl) => bool true;
      le `i64 x (i64 0xffff_ffff_ffff_ffffL) => bool true;
      (* unsigned x > 0xff... = false *)
      gt `i8 x (i8 0xff) => bool false;
      gt `i16 x (i16 0xffff) => bool false;
      gt `i32 x (i32 0xffff_ffffl) => bool false;
      gt `i64 x (i64 0xffff_ffff_ffff_ffffL) => bool false;
      (* unsigned x >= 0xff... = x == 0xff... *)
      ge `i8 x (i8 0xff) => eq `i8 x (i8 0xff);
      ge `i16 x (i16 0xffff) => eq `i16 x (i16 0xffff);
      ge `i32 x (i32 0xffff_ffffl) => eq `i32 x (i32 0xffff_ffffl);
      ge `i64 x (i64 0xffff_ffff_ffff_ffffL) => eq `i64 x (i64 0xffff_ffff_ffff_ffffL);
      (* signed x < 0x80... = false *)
      slt `i8 x (i8 0x80) => bool false;
      slt `i16 x (i16 0x8000) => bool false;
      slt `i32 x (i32 0x8000_0000l) => bool false;
      slt `i64 x (i64 0x8000_0000_0000_0000L) => bool false;
      (* signed x <= 0x80... = x == 0x80... *)
      sle `i8 x (i8 0x80) => eq `i8 x (i8 0x80);
      sle `i16 x (i16 0x8000) => eq `i16 x (i16 0x8000);
      sle `i32 x (i32 0x8000_0000l) => eq `i32 x (i32 0x8000_0000l);
      sle `i64 x (i64 0x8000_0000_0000_0000L) => eq `i64 x (i64 0x8000_0000_0000_0000L);
      (* signed x > 0x80... = x != 0x80... *)
      sgt `i8 x (i8 0x80) => ne `i8 x (i8 0x80);
      sgt `i16 x (i16 0x8000) => ne `i16 x (i16 0x8000);
      sgt `i32 x (i32 0x8000_0000l) => ne `i32 x (i32 0x8000_0000l);
      sgt `i64 x (i64 0x8000_0000_0000_0000L) => ne `i64 x (i64 0x8000_0000_0000_0000L);
      (* signed x >= 0x80... = true *)
      sge `i8 x (i8 0x80) => bool true;
      sge `i16 x (i16 0x8000) => bool true;
      sge `i32 x (i32 0x8000_0000l) => bool true;
      sge `i64 x (i64 0x8000_0000_0000_0000L) => bool true;
      (* signed x > 0x7f... = false *)
      sgt `i8 x (i8 0x7f) => bool false;
      sgt `i16 x (i16 0x7fff) => bool false;
      sgt `i32 x (i32 0x7fff_ffffl) => bool false;
      sgt `i64 x (i64 0x7fff_ffff_ffff_ffffL) => bool false;
      (* signed x >= 0x7f... = x == 0x7f... *)
      sge `i8 x (i8 0x7f) => eq `i8 x (i8 0x7f);
      sge `i16 x (i16 0x7fff) => eq `i16 x (i16 0x7fff);
      sge `i32 x (i32 0x7fff_ffffl) => eq `i32 x (i32 0x7fff_ffffl);
      sge `i64 x (i64 0x7fff_ffff_ffff_ffffL) => eq `i64 x (i64 0x7fff_ffff_ffff_ffffL);
      (* signed x < 0x7f... = x != 0x7f... *)
      slt `i8 x (i8 0x7f) => ne `i8 x (i8 0x7f);
      slt `i16 x (i16 0x7fff) => ne `i16 x (i16 0x7fff);
      slt `i32 x (i32 0x7fff_ffffl) => ne `i32 x (i32 0x7fff_ffffl);
      slt `i64 x (i64 0x7fff_ffff_ffff_ffffL) => ne `i64 x (i64 0x7fff_ffff_ffff_ffffL);
      (* signed x <= 0x7f... = true *)
      sle `i8 x (i8 0x7f) => bool true;
      sle `i16 x (i16 0x7fff) => bool true;
      sle `i32 x (i32 0x7fff_ffffl) => bool true;
      sle `i64 x (i64 0x7fff_ffff_ffff_ffffL) => bool true;
      (* signed (zext x) < 0 = false when x has a smaller type *)
      (slt `i16 (zext `i16 x) (i16 0) =>? bool false) ~if_:(has_type_x `i8);
      (slt `i32 (zext `i32 x) (i32 0l) =>? bool false) ~if_:(has_type_x `i8);
      (slt `i32 (zext `i32 x) (i32 0l) =>? bool false) ~if_:(has_type_x `i16);
      (slt `i64 (zext `i64 x) (i64 0L) =>? bool false) ~if_:(has_type_x `i8);
      (slt `i64 (zext `i64 x) (i64 0L) =>? bool false) ~if_:(has_type_x `i16);
      (slt `i64 (zext `i64 x) (i64 0L) =>? bool false) ~if_:(has_type_x `i32);
      (* signed (zext x) >= 0 = true when x has a smaller type *)
      (sge `i16 (zext `i16 x) (i16 0) =>? bool true) ~if_:(has_type_x `i8);
      (sge `i32 (zext `i32 x) (i32 0l) =>? bool true) ~if_:(has_type_x `i8);
      (sge `i32 (zext `i32 x) (i32 0l) =>? bool true) ~if_:(has_type_x `i16);
      (sge `i64 (zext `i64 x) (i64 0L) =>? bool true) ~if_:(has_type_x `i8);
      (sge `i64 (zext `i64 x) (i64 0L) =>? bool true) ~if_:(has_type_x `i16);
      (sge `i64 (zext `i64 x) (i64 0L) =>? bool true) ~if_:(has_type_x `i32);
      (* flag x == 1 = x *)
      eq `i8 (flag `i8 x) (i8 1) => x;
      eq `i16 (flag `i16 x) (i16 1) => x;
      eq `i32 (flag `i32 x) (i32 1l) => x;
      eq `i64 (flag `i64 x) (i64 1L) => x;
      (* flag x == 0 = (flag x ^ 1) == 1 *)
      eq `i8 (flag `i8 x) (i8 0) => eq `i8 (xor `i8 (flag `i8 x) (i8 1)) (i8 1);
      eq `i16 (flag `i16 x) (i16 0) => eq `i16 (xor `i16 (flag `i16 x) (i16 1)) (i16 1);
      eq `i32 (flag `i32 x) (i32 0l) => eq `i32 (xor `i32 (flag `i32 x) (i32 1l)) (i32 1l);
      eq `i64 (flag `i64 x) (i64 0L) => eq `i64 (xor `i64 (flag `i64 x) (i64 1L)) (i64 1L);
      (* flag x != 1 = flag == 0 *)
      ne `i8 (flag `i8 x) (i8 1) => eq `i8 (flag `i8 x) (i8 0);
      ne `i16 (flag `i16 x) (i16 1) => eq `i16 (flag `i16 x) (i16 0);
      ne `i32 (flag `i32 x) (i32 1l) => eq `i32 (flag `i32 x) (i32 0l);
      ne `i64 (flag `i64 x) (i64 1L) => eq `i64 (flag `i64 x) (i64 0L);
      (* flag x != 0 = x *)
      ne `i8 (flag `i8 x) (i8 0) => x;
      ne `i16 (flag `i16 x) (i16 0) => x;
      ne `i32 (flag `i32 x) (i32 0l) => x;
      ne `i64 (flag `i64 x) (i64 0L) => x;
      (* flag x <= 0 = flag x == 0 *)
      le `i8 (flag `i8 x) (i8 0) => eq `i8 (flag `i8 x) (i8 0);
      le `i16 (flag `i16 x) (i16 0) => eq `i16 (flag `i16 x) (i16 0);
      le `i32 (flag `i32 x) (i32 0l) => eq `i32 (flag `i32 x) (i32 0l);
      le `i64 (flag `i64 x) (i64 0L) => eq `i64 (flag `i64 x) (i64 0L);
      (* flag x <= 1 = true *)
      le `i8 (flag `i8 x) (i8 1) => bool true;
      le `i16 (flag `i16 x) (i16 1) => bool true;
      le `i32 (flag `i32 x) (i32 1l) => bool true;
      le `i64 (flag `i64 x) (i64 1L) => bool true;
      (* signed flag x <= 1 = true *)
      sle `i8 (flag `i8 x) (i8 1) => bool true;
      sle `i16 (flag `i16 x) (i16 1) => bool true;
      sle `i32 (flag `i32 x) (i32 1l) => bool true;
      sle `i64 (flag `i64 x) (i64 1L) => bool true;
      (* signed flag x <= 0 = true *)
      sle `i8 (flag `i8 x) (i8 0) => bool true;
      sle `i16 (flag `i16 x) (i16 0) => bool true;
      sle `i32 (flag `i32 x) (i32 0l) => bool true;
      sle `i64 (flag `i64 x) (i64 0L) => bool true;
      (* flag x < 1 = flag x == 0 *)
      lt `i8 (flag `i8 x) (i8 1) => eq `i8 (flag `i8 x) (i8 0);
      lt `i16 (flag `i16 x) (i16 1) => eq `i16 (flag `i16 x) (i16 0);
      lt `i32 (flag `i32 x) (i32 1l) => eq `i32 (flag `i32 x) (i32 0l);
      lt `i64 (flag `i64 x) (i64 1L) => eq `i64 (flag `i64 x) (i64 0L);
      (* signed flag < 1 = flag x == 0 *)
      slt `i8 (flag `i8 x) (i8 1) => eq `i8 (flag `i8 x) (i8 0);
      slt `i16 (flag `i16 x) (i16 1) => eq `i16 (flag `i16 x) (i16 0);
      slt `i32 (flag `i32 x) (i32 1l) => eq `i32 (flag `i32 x) (i32 0l);
      slt `i64 (flag `i64 x) (i64 1L) => eq `i64 (flag `i64 x) (i64 0L);
      (* signed flag x < 0 = false *)
      slt `i8 (flag `i8 x) (i8 0) => bool false;
      slt `i16 (flag `i16 x) (i16 0) => bool false;
      slt `i32 (flag `i32 x) (i32 0l) => bool false;
      slt `i64 (flag `i64 x) (i64 0L) => bool false;
      (* flag x >= 0 = true *)
      ge `i8 (flag `i8 x) (i8 0) => bool true;
      ge `i16 (flag `i16 x) (i16 0) => bool true;
      ge `i32 (flag `i32 x) (i32 0l) => bool true;
      ge `i64 (flag `i64 x) (i64 0L) => bool true;
      (* signed flag >= 0 = true *)
      sge `i8 (flag `i8 x) (i8 0) => bool true;
      sge `i16 (flag `i16 x) (i16 0) => bool true;
      sge `i32 (flag `i32 x) (i32 0l) => bool true;
      sge `i64 (flag `i64 x) (i64 0L) => bool true;
      (* flag x >= 1 = flag x == 1 *)
      ge `i8 (flag `i8 x) (i8 1) => eq `i8 (flag `i8 x) (i8 1);
      ge `i16 (flag `i16 x) (i16 1) => eq `i16 (flag `i16 x) (i16 1);
      ge `i32 (flag `i32 x) (i32 1l) => eq `i32 (flag `i32 x) (i32 1l);
      ge `i64 (flag `i64 x) (i64 1L) => eq `i64 (flag `i64 x) (i64 1L);
      (* signed flag x >= 1 = flag x == 1 *)
      sge `i8 (flag `i8 x) (i8 1) => eq `i8 (flag `i8 x) (i8 1);
      sge `i16 (flag `i16 x) (i16 1) => eq `i16 (flag `i16 x) (i16 1);
      sge `i32 (flag `i32 x) (i32 1l) => eq `i32 (flag `i32 x) (i32 1l);
      sge `i64 (flag `i64 x) (i64 1L) => eq `i64 (flag `i64 x) (i64 1L);
      (* flag x > 0 = flag x == 1 *)
      gt `i8 (flag `i8 x) (i8 0) => eq `i8 (flag `i8 x) (i8 1);
      gt `i16 (flag `i16 x) (i16 0) => eq `i16 (flag `i16 x) (i16 1);
      gt `i32 (flag `i32 x) (i32 0l) => eq `i32 (flag `i32 x) (i32 1l);
      gt `i64 (flag `i64 x) (i64 0L) => eq `i64 (flag `i64 x) (i64 1L);
      (* signed flag x > 0 = flag x == 1 *)
      sgt `i8 (flag `i8 x) (i8 0) => eq `i8 (flag `i8 x) (i8 1);
      sgt `i16 (flag `i16 x) (i16 0) => eq `i16 (flag `i16 x) (i16 1);
      sgt `i32 (flag `i32 x) (i32 0l) => eq `i32 (flag `i32 x) (i32 1l);
      sgt `i64 (flag `i64 x) (i64 0L) => eq `i64 (flag `i64 x) (i64 1L);
      (* flag x > 1 = false *)
      gt `i8 (flag `i8 x) (i8 1) => bool false;
      gt `i16 (flag `i16 x) (i16 1) => bool false;
      gt `i32 (flag `i32 x) (i32 1l) => bool false;
      gt `i64 (flag `i64 x) (i64 1L) => bool false;
      (* signed flag x > 1 = false *)
      sgt `i8 (flag `i8 x) (i8 1) => bool false;
      sgt `i16 (flag `i16 x) (i16 1) => bool false;
      sgt `i32 (flag `i32 x) (i32 1l) => bool false;
      sgt `i64 (flag `i64 x) (i64 1L) => bool false;
      (* flag `cmp` y = false when y not bool *)
      (eq `i8 (flag `i8 x) y =>? bool false) ~if_:is_not_bool_y;
      (eq `i16 (flag `i16 x) y =>? bool false) ~if_:is_not_bool_y;
      (eq `i32 (flag `i32 x) y =>? bool false) ~if_:is_not_bool_y;
      (eq `i64 (flag `i64 x) y =>? bool false) ~if_:is_not_bool_y;
      (ne `i8 (flag `i8 x) y =>? bool false) ~if_:is_not_bool_y;
      (ne `i16 (flag `i16 x) y =>? bool false) ~if_:is_not_bool_y;
      (ne `i32 (flag `i32 x) y =>? bool false) ~if_:is_not_bool_y;
      (ne `i64 (flag `i64 x) y =>? bool false) ~if_:is_not_bool_y;
      (lt `i8 (flag `i8 x) y =>? bool false) ~if_:is_not_bool_y;
      (lt `i16 (flag `i16 x) y =>? bool false) ~if_:is_not_bool_y;
      (lt `i32 (flag `i32 x) y =>? bool false) ~if_:is_not_bool_y;
      (lt `i64 (flag `i64 x) y =>? bool false) ~if_:is_not_bool_y;
      (slt `i8 (flag `i8 x) y =>? bool false) ~if_:is_not_bool_y;
      (slt `i16 (flag `i16 x) y =>? bool false) ~if_:is_not_bool_y;
      (slt `i32 (flag `i32 x) y =>? bool false) ~if_:is_not_bool_y;
      (slt `i64 (flag `i64 x) y =>? bool false) ~if_:is_not_bool_y;
      (le `i8 (flag `i8 x) y =>? bool false) ~if_:is_not_bool_y;
      (le `i16 (flag `i16 x) y =>? bool false) ~if_:is_not_bool_y;
      (le `i32 (flag `i32 x) y =>? bool false) ~if_:is_not_bool_y;
      (le `i64 (flag `i64 x) y =>? bool false) ~if_:is_not_bool_y;
      (sle `i8 (flag `i8 x) y =>? bool false) ~if_:is_not_bool_y;
      (sle `i16 (flag `i16 x) y =>? bool false) ~if_:is_not_bool_y;
      (sle `i32 (flag `i32 x) y =>? bool false) ~if_:is_not_bool_y;
      (sle `i64 (flag `i64 x) y =>? bool false) ~if_:is_not_bool_y;
      (gt `i8 (flag `i8 x) y =>? bool false) ~if_:is_not_bool_y;
      (gt `i16 (flag `i16 x) y =>? bool false) ~if_:is_not_bool_y;
      (gt `i32 (flag `i32 x) y =>? bool false) ~if_:is_not_bool_y;
      (gt `i64 (flag `i64 x) y =>? bool false) ~if_:is_not_bool_y;
      (sgt `i8 (flag `i8 x) y =>? bool false) ~if_:is_not_bool_y;
      (sgt `i16 (flag `i16 x) y =>? bool false) ~if_:is_not_bool_y;
      (sgt `i32 (flag `i32 x) y =>? bool false) ~if_:is_not_bool_y;
      (sgt `i64 (flag `i64 x) y =>? bool false) ~if_:is_not_bool_y;
      (ge `i8 (flag `i8 x) y =>? bool false) ~if_:is_not_bool_y;
      (ge `i16 (flag `i16 x) y =>? bool false) ~if_:is_not_bool_y;
      (ge `i32 (flag `i32 x) y =>? bool false) ~if_:is_not_bool_y;
      (ge `i64 (flag `i64 x) y =>? bool false) ~if_:is_not_bool_y;
      (sge `i8 (flag `i8 x) y =>? bool false) ~if_:is_not_bool_y;
      (sge `i16 (flag `i16 x) y =>? bool false) ~if_:is_not_bool_y;
      (sge `i32 (flag `i32 x) y =>? bool false) ~if_:is_not_bool_y;
      (sge `i64 (flag `i64 x) y =>? bool false) ~if_:is_not_bool_y;
      (* extend t1 (flag t2 x) = flag t1 x *)
      sext `i16 (flag `i8 x) => flag `i16 x;
      sext `i32 (flag `i8 x) => flag `i32 x;
      sext `i32 (flag `i16 x) => flag `i32 x;
      sext `i64 (flag `i8 x) => flag `i64 x;
      sext `i64 (flag `i16 x) => flag `i64 x;
      sext `i64 (flag `i32 x) => flag `i64 x;
      zext `i16 (flag `i8 x) => flag `i16 x;
      zext `i32 (flag `i8 x) => flag `i32 x;
      zext `i32 (flag `i16 x) => flag `i32 x;
      zext `i64 (flag `i8 x) => flag `i64 x;
      zext `i64 (flag `i16 x) => flag `i64 x;
      zext `i64 (flag `i32 x) => flag `i64 x;
      (* itrunc t1 (flag t2 x) = flag t1 x *)
      itrunc `i8 (flag `i16 x) => flag `i8 x;
      itrunc `i8 (flag `i32 x) => flag `i8 x;
      itrunc `i8 (flag `i64 x) => flag `i8 x;
      itrunc `i16 (flag `i32 x) => flag `i16 x;
      itrunc `i16 (flag `i64 x) => flag `i16 x;
      itrunc `i32 (flag `i64 x) => flag `i32 x;
      (* extend i8 x = x *)
      sext `i8 x => x;
      zext `i8 x => x;
      (* extend (extend x) = extend x *)
      sext `i16 (sext `i16 x) => sext `i16 x;
      sext `i32 (sext `i16 x) => sext `i32 x;
      sext `i32 (sext `i32 x) => sext `i32 x;
      sext `i64 (sext `i16 x) => sext `i64 x;
      sext `i64 (sext `i32 x) => sext `i64 x;
      sext `i64 (sext `i64 x) => sext `i64 x;
      zext `i16 (zext `i16 x) => zext `i16 x;
      zext `i32 (zext `i16 x) => zext `i32 x;
      zext `i32 (zext `i32 x) => zext `i32 x;
      zext `i64 (zext `i16 x) => zext `i64 x;
      zext `i64 (zext `i32 x) => zext `i64 x;
      zext `i64 (zext `i64 x) => zext `i64 x;
      (* extend x to original type = x *)
      sext `i16 x =>* identity_same_type_x `i16;
      zext `i16 x =>* identity_same_type_x `i16;
      sext `i32 x =>* identity_same_type_x `i32;
      zext `i32 x =>* identity_same_type_x `i32;
      sext `i64 x =>* identity_same_type_x `i64;
      zext `i64 x =>* identity_same_type_x `i64;
      (* itrunc i64 x = x *)
      itrunc `i64 x => x;
      (* itrunc x to original type = x *)
      itrunc `i8 x =>* identity_same_type_x `i8;
      itrunc `i16 x =>* identity_same_type_x `i16;
      itrunc `i32 x =>* identity_same_type_x `i32;
      (* itrunc (sext/zext x) to original type = x; these are the cases
         not covered by the general case above. *)
      itrunc `i8 (sext `i16 x) =>* identity_same_type_x `i8;
      itrunc `i8 (zext `i16 x) =>* identity_same_type_x `i8;
      itrunc `i8 (sext `i32 x) =>* identity_same_type_x `i8;
      itrunc `i8 (zext `i32 x) =>* identity_same_type_x `i8;
      itrunc `i8 (sext `i64 x) =>* identity_same_type_x `i8;
      itrunc `i8 (zext `i64 x) =>* identity_same_type_x `i8;
      itrunc `i16 (sext `i32 x) =>* identity_same_type_x `i16;
      itrunc `i16 (zext `i32 x) =>* identity_same_type_x `i16;
      itrunc `i16 (sext `i64 x) =>* identity_same_type_x `i16;
      itrunc `i16 (zext `i64 x) =>* identity_same_type_x `i16;
      itrunc `i32 (sext `i64 x) =>* identity_same_type_x `i32;
      itrunc `i32 (zext `i64 x) =>* identity_same_type_x `i32;
      (* br true, x, y = jmp x *)
      br (bool true) x y => jmp x;
      (* br false, x, y = jmp y *)
      br (bool false) x y => jmp y;
      (* br x, y, y = jmp y. *)
      br x y y => jmp y;
      (* true ? x : y = x. *)
      sel `i8 (bool true) x y => x;
      sel `i16 (bool true) x y => x;
      sel `i32 (bool true) x y => x;
      sel `i64 (bool true) x y => x;
      sel `f32 (bool true) x y => x;
      sel `f64 (bool true) x y => x;
      (* false ? x : y = y *)
      sel `i8 (bool false) x y => y;
      sel `i16 (bool false) x y => y;
      sel `i32 (bool false) x y => y;
      sel `i64 (bool false) x y => y;
      sel `f32 (bool false) x y => y;
      sel `f64 (bool false) x y => y;
      (* x ? y : y = y. *)
      sel `i8 x y y => y;
      sel `i16 x y y => y;
      sel `i32 x y y => y;
      sel `i64 x y y => y;
      sel `f32 x y y => y;
      sel `f64 x y y => y;
      (* Specialize to `flag`. *)
      sel `i8 x (i8 1) (i8 0) => flag `i8 x;
      sel `i16 x (i16 1) (i16 0) => flag `i16 x;
      sel `i32 x (i32 1l) (i32 0l) => flag `i32 x;
      sel `i64 x (i64 1L) (i64 0L) => flag `i64 x;
      sel `i8 x (i8 0)  (i8 1) => xor `i8 (flag `i8 x) (i8 1);
      sel `i16 x (i16 0) (i16 1) => xor `i16 (flag `i16 x) (i16 1);
      sel `i32 x (i32 0l) (i32 1l) => xor `i32 (flag `i32 x) (i32 1l);
      sel `i64 x (i64 0L) (i64 1L) => xor `i64 (flag `i64 x) (i64 1L);
      (* Copy propagation. *)
      copy `i8 x => x;
      copy `i16 x => x;
      copy `i32 x => x;
      copy `i64 x => x;
      copy `f32 x => x;
      copy `f64 x => x;
    ]
end

let run tenv fn = Egraph.run fn tenv Rules.rules
