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
        let* i = Subst.interval s in
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
        let+ i = Subst.interval s in
        not I.(contains_value i Bv.one || contains_value i Bv.zero)
    end

  (* `x` is (signed) greater than 1 *)
  let is_sgt_one x env =
    Option.value ~default:false begin
      let* s = Subst.find env x in
      match Subst.const s with
      | Some `int (i, ty) ->
        let m = Bv.modulus @@ Type.sizeof_imm ty in
        Some (Bv.signed_compare i Bv.one m > 0)
      | _ ->
        let+ i = Subst.interval s in
        let m = Bv.modulus @@ I.size i in
        Bv.signed_compare (I.signed_min i) Bv.one m > 0
    end

  (* `x` is (signed) less than 0 *)
  let is_slt_zero x env =
    Option.value ~default:false begin
      let* s = Subst.find env x in
      match Subst.const s with
      | Some `int (i, ty) ->
        let m = Bv.modulus @@ Type.sizeof_imm ty in
        Some (Bv.signed_compare i Bv.zero m < 0)
      | _ ->
        let+ i = Subst.interval s in
        let m = Bv.modulus @@ I.size i in
        Bv.signed_compare (I.signed_max i) Bv.zero m < 0
    end

  let has_type x ty env =
    Subst.find env x |>
    Option.bind ~f:Subst.typeof |> function
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
        let module B = (val bv ty) in
        let sz = Type.sizeof_imm ty - 1 in
        O.guard begin
          not (B.msb a) &&
          Bv.(a <= b) &&
          Bv.(b = B.int sz)
        end
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
      let module B = (val bv ty) in
      let+ () = O.guard begin
          let open Bv in
          let open B in
          i <> pred zero &&
          i <> zero &&
          i <> one &&
          (i land pred i) <> zero
        end in
      let sz1 = Type.sizeof_imm ty - 1 in
      let s_mul, s_shr = Magic_div.signed i ty in
      let tb = (ty :> Type.basic) in
      let q1 = Op.(mulh ty x (int s_mul ty)) in
      let q2 =
        if not (B.msb i) && B.msb s_mul then
          Op.add tb q1 x
        else if B.msb i && not (B.msb s_mul) then
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
      let module B = (val bv ty) in
      let+ () = O.guard begin
          let open Bv in
          let open B in
          i <> pred zero &&
          i <> zero &&
          i <> one &&
          (i land pred i) <> zero
        end in
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
      let module B = (val bv ty) in
      let+ () = O.guard begin
          let open Bv in
          let open B in
          i <> pred zero &&
          i <> zero &&
          i <> one &&
          (i land pred i) <> zero
        end in
      let tb = (ty :> Type.basic) in
      let n = Bv.to_int64 i in
      let n' = Int64.pred n in
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
    let* tx = Subst.find env x >>= Subst.typeof in
    let+ () = O.guard @@ Type.equal tx (ty :> Type.t) in
    var x

  let cannot_be_zero x env = Option.is_some begin
      let* s = Subst.find env x in
      match Subst.const s with
      | Some `int (i, _) -> O.guard @@ Bv.(i <> zero)
      | _ ->
        let* i = Subst.interval s in
        O.guard @@ not @@ I.contains_value i Bv.zero
    end

  let is_rotate_const x y env =
    Option.is_some begin
      let* xi = Subst.find env x >>= Subst.const in
      let* yi = Subst.find env y >>= Subst.const in
      match xi, yi with
      | `int (xi, xt), `int (yi, yt) when Type.equal_imm xt yt ->
        let xi = Bv.to_int64 xi in
        let yi = Bv.to_int64 yi in
        let sz = Int.to_int64 @@ Type.sizeof_imm xt in
        Option.some_if Int64.(xi = sz - yi) ()
      | _ -> None
    end

  let x = var "x"
  let y = var "y"
  let z = var "z"

  let is_const_x = is_const "x"
  let is_const_y = is_const "y"
  let is_not_const_y = is_not_const "y"
  let is_neg_const_y = is_neg_const "y"
  let is_not_bool_y = is_not_bool "y"
  let is_sgt_one_y = is_sgt_one "y"
  let is_slt_zero_y = is_slt_zero "y"
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
  let is_rotate_const_y_z = is_rotate_const "y" "z"

  (* Sets of related rules. *)
  module Groups = struct
    open Op

    (* Commutativity of constants. *)
    let commute_consts = [
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
    ]

    (* Enable constant folding via associativity. *)
    let assoc_consts = [
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
    ]

    (* x + (-y) = x - y when y is a constant *)
    let add_neg_const = [
      (add `i8 x y =>? sub `i8 x (neg `i8 y)) ~if_:is_neg_const_y;
      (add `i16 x y =>? sub `i16 x (neg `i16 y)) ~if_:is_neg_const_y;
      (add `i32 x y =>? sub `i32 x (neg `i32 y)) ~if_:is_neg_const_y;
      (add `i64 x y =>? sub `i64 x (neg `i64 y)) ~if_:is_neg_const_y;
    ]

    (* x - (-y) = x + y when y is a constant *)
    let sub_neg_const = [
      (sub `i8 x y =>? add `i8 x (neg `i8 y)) ~if_:is_neg_const_y;
      (sub `i16 x y =>? add `i16 x (neg `i16 y)) ~if_:is_neg_const_y;
      (sub `i32 x y =>? add `i32 x (neg `i32 y)) ~if_:is_neg_const_y;
      (sub `i64 x y =>? add `i64 x (neg `i64 y)) ~if_:is_neg_const_y;
    ]

    (* x + (-y) = (-y) + x = x - y *)
    let add_neg = [
      (add `i8 x (neg `i8 y) =>? sub `i8 x y) ~if_:is_not_const_y;
      (add `i16 x (neg `i16 y) =>? sub `i16 x y) ~if_:is_not_const_y;
      (add `i32 x (neg `i32 y) =>? sub `i32 x y) ~if_:is_not_const_y;
      (add `i64 x (neg `i64 y) =>? sub `i64 x y) ~if_:is_not_const_y;
      (add `i8 (neg `i8 y) x =>? sub `i8 x y) ~if_:is_not_const_y;
      (add `i16 (neg `i16 y) x =>? sub `i16 x y) ~if_:is_not_const_y;
      (add `i32 (neg `i32 y) x =>? sub `i32 x y) ~if_:is_not_const_y;
      (add `i64 (neg `i64 y) x =>? sub `i64 x y) ~if_:is_not_const_y;
    ]

    (* x - (-y) = x + y *)
    let sub_neg = [
      (sub `i8 x (neg `i8 y) =>? add `i8 x y) ~if_:is_not_const_y;
      (sub `i16 x (neg `i16 y) =>? add `i16 x y) ~if_:is_not_const_y;
      (sub `i32 x (neg `i32 y) =>? add `i32 x y) ~if_:is_not_const_y;
      (sub `i64 x (neg `i64 y) =>? add `i64 x y) ~if_:is_not_const_y;
    ]

    (* x + 0 = x. *)
    let add_zero = [
      add `i8 x  (i8 0) => x;
      add `i16 x (i16 0) => x;
      add `i32 x (i32 0l) => x;
      add `i64 x (i64 0L) => x;
    ]

    (* x - 0 = x. *)
    let sub_zero = [
      sub `i8 x  (i8 0) => x;
      sub `i16 x (i16 0) => x;
      sub `i32 x (i32 0l) => x;
      sub `i64 x (i64 0L) => x;
    ]

    (* 0 - x = -x *)
    let sub_zero_neg = [
      sub `i8  (i8 0) x => neg `i8 x;
      sub `i16 (i16 0) x => neg `i16 x;
      sub `i32 (i32 0l) x => neg `i32 x;
      sub `i64 (i64 0L) x => neg `i64 x;
    ]

    (* -(-x) = x *)
    let double_neg = [
      neg `i8 (neg `i8 x) => x;
      neg `i16 (neg `i16 x) => x;
      neg `i32 (neg `i32 x) => x;
      neg `i64 (neg `i64 x) => x;
    ]

    (* ~(~x) = x *)
    let double_not = [
      not_ `i8 (not_ `i8 x) => x;
      not_ `i16 (not_ `i16 x) => x;
      not_ `i32 (not_ `i32 x) => x;
      not_ `i64 (not_ `i64 x) => x;
    ]

    (* ~x + 1 = 1 + ~x = -x *)
    let inc_not = [
      add `i8 (not_ `i8 x) (i8 1) => neg `i8 x;
      add `i16 (not_ `i16 x) (i16 1) => neg `i16 x;
      add `i32 (not_ `i32 x) (i32 1l) => neg `i32 x;
      add `i64 (not_ `i64 x) (i64 1L) => neg `i64 x;
      add `i8 (i8 1) (not_ `i8 x) => neg `i8 x;
      add `i16 (i16 1) (not_ `i16 x) => neg `i16 x;
      add `i32 (i32 1l) (not_ `i32 x) => neg `i32 x;
      add `i64 (i64 1L) (not_ `i64 x) => neg `i64 x;
    ]

    (* -x * -y = x * y *)
    let mul_negs = [
      mul `i8 (neg `i8 x) (neg `i8 y) => mul `i8 x y;
      mul `i16 (neg `i16 x) (neg `i16 y) => mul `i16 x y;
      mul `i32 (neg `i32 x) (neg `i32 y) => mul `i32 x y;
      mul `i64 (neg `i64 x) (neg `i64 y) => mul `i64 x y;
    ]

    (* x - x = 0. *)
    let sub_self = [
      sub `i8 x x =>  i8 0;
      sub `i16 x x => i16 0;
      sub `i32 x x => i32 0l;
      sub `i64 x x => i64 0L;
    ]

    (* x * 0 = 0. *)
    let mul_zero = [
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
    ]

    (* x * 1 = x *)
    let mul_one = [
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
    ]

    (* x * -1 = -x *)
    let mul_neg_one = [
      mul `i8 x  (i8 (-1)) => neg `i8 x;
      mul `i16 x (i16 (-1)) => neg `i16 x;
      mul `i32 x (i32 (-1l)) => neg `i32 x;
      mul `i64 x (i64 (-1L)) => neg `i64 x;
    ]

    (* x * 2 = x + x *)
    let mul_two_add_self = [
      mul `i8  x (i8 2) => add `i8 x x;
      mul `i16 x (i16 2) => add `i16 x x;
      mul `i32 x (i32 2l) => add `i32 x x;
      mul `i64  x(i64 2L) => add `i64 x x;
    ]

    (* x * c = x << log2(c) when c is a constant *)
    let mul_pow2 = [
      mul `i8 x y =>* mul_imm_pow2_y;
      mul `i16 x y =>* mul_imm_pow2_y;
      mul `i32 x y =>* mul_imm_pow2_y;
      mul `i64 x y =>* mul_imm_pow2_y;
      mul `i8 x y =>* mul_imm_non_pow2_y;
      mul `i16 x y =>* mul_imm_non_pow2_y;
      mul `i32 x y =>* mul_imm_non_pow2_y;
      mul `i64 x y =>* mul_imm_non_pow2_y;
    ]

    (* signed x / c when c is constant power of 2 *)
    let sdiv_const_pow2 = [
      div `i8 x y =>* div_imm_pow2_y;
      div `i16 x y =>* div_imm_pow2_y;
      div `i32 x y =>* div_imm_pow2_y;
      div `i64 x y =>* div_imm_pow2_y;
    ]

    (* signed x / c when c is constant non-power of 2 *)
    let sdiv_const_non_pow2 = [
      div `i8 x y =>* div_imm_non_pow2_y;
      div `i16 x y =>* div_imm_non_pow2_y;
      div `i32 x y =>* div_imm_non_pow2_y;
      div `i64 x y =>* div_imm_non_pow2_y;
    ]

    (* signed x % c when c is a constant power of 2 *)
    let srem_const_pow2 = [
      rem `i8 x y =>* rem_imm_pow2_y;
      rem `i16 x y =>* rem_imm_pow2_y;
      rem `i32 x y =>* rem_imm_pow2_y;
      rem `i64 x y =>* rem_imm_pow2_y;
    ]

    (* signed x % c when c is a constant non-power of 2 *)
    let srem_const_non_pow2 = [
      rem `i8 x y =>* rem_imm_non_pow2_y;
      rem `i16 x y =>* rem_imm_non_pow2_y;
      rem `i32 x y =>* rem_imm_non_pow2_y;
      rem `i64 x y =>* rem_imm_non_pow2_y;
    ]

    (* unsigned x / c when c is a constant power of 2 *)
    let udiv_const_pow2 = [
      udiv `i8 x y =>* udiv_imm_pow2_y;
      udiv `i16 x y =>* udiv_imm_pow2_y;
      udiv `i32 x y =>* udiv_imm_pow2_y;
      udiv `i64 x y =>* udiv_imm_pow2_y;
    ]

    (* unsigned x / c when c is a constant non-power of 2 *)
    let udiv_const_non_pow2 = [
      udiv `i8 x y =>* udiv_imm_non_pow2_y;
      udiv `i16 x y =>* udiv_imm_non_pow2_y;
      udiv `i32 x y =>* udiv_imm_non_pow2_y;
      udiv `i64 x y =>* udiv_imm_non_pow2_y;
    ]

    (* unsigned x % c when c is a constant power of 2 *)
    let urem_const_pow2 = [
      urem `i8 x y =>* urem_imm_pow2_y;
      urem `i16 x y =>* urem_imm_pow2_y;
      urem `i32 x y =>* urem_imm_pow2_y;
      urem `i64 x y =>* urem_imm_pow2_y;
    ]

    (* unsigned x % c when c is a constant non-power of 2 *)
    let urem_const_non_pow2 = [
      urem `i8 x y =>* urem_imm_non_pow2_y;
      urem `i16 x y =>* urem_imm_non_pow2_y;
      urem `i32 x y =>* urem_imm_non_pow2_y;
      urem `i64 x y =>* urem_imm_non_pow2_y;
    ]

    (* x / 1 = x *)
    let div_one = [
      div `i8  x (i8 1) => x;
      div `i16 x (i16 1) => x;
      div `i32 x (i32 1l) => x;
      div `i64 x (i64 1L) => x;
      udiv `i8 x (i8 1) => x;
      udiv `i16 x (i16 1) => x;
      udiv `i32 x (i32 1l) => x;
      udiv `i64 x (i64 1L) => x;
    ]

    (* x / x = 1 when x cannot be zero *)
    let div_self = [
      (div `i8 x x =>? i8 1) ~if_:cannot_be_zero_x;
      (div `i16 x x =>? i16 1) ~if_:cannot_be_zero_x;
      (div `i32 x x =>? i32 1l) ~if_:cannot_be_zero_x;
      (div `i64 x x =>? i64 1L) ~if_:cannot_be_zero_x;
      (udiv `i8 x x =>? i8 1) ~if_:cannot_be_zero_x;
      (udiv `i16 x x =>? i16 1) ~if_:cannot_be_zero_x;
      (udiv `i32 x x =>? i32 1l) ~if_:cannot_be_zero_x;
      (udiv `i64 x x =>? i64 1L) ~if_:cannot_be_zero_x;
    ]

    (* x % x = 0 when x cannot be zero *)
    let rem_self = [
      (rem `i8 x x =>? i8 0) ~if_:cannot_be_zero_x;
      (rem `i16 x x =>? i16 0) ~if_:cannot_be_zero_x;
      (rem `i32 x x =>? i32 0l) ~if_:cannot_be_zero_x;
      (rem `i64 x x =>? i64 0L) ~if_:cannot_be_zero_x;
      (urem `i8 x x =>? i8 0) ~if_:cannot_be_zero_x;
      (urem `i16 x x =>? i16 0) ~if_:cannot_be_zero_x;
      (urem `i32 x x =>? i32 0l) ~if_:cannot_be_zero_x;
      (urem `i64 x x =>? i64 0L) ~if_:cannot_be_zero_x;
    ]

    (* signed x / -1 = -x *)
    let sdiv_neg_one = [
      div `i8 x (i8 (-1)) => neg `i8 x;
      div `i16 x (i16 (-1)) => neg `i16 x;
      div `i32 x (i32 (-1l)) => neg `i32 x;
      div `i64 x (i64 (-1L)) => neg `i64 x;
    ]

    (* signed x % -1 = 0 *)
    let srem_neg_one = [
      rem `i8 x (i8 (-1)) => i8 0;
      rem `i16 x (i16 (-1)) => i16 0;
      rem `i32 x (i32 (-1l)) => i32 0l;
      rem `i64 x (i64 (-1L)) => i64 0L;
    ]

    (* unsigned x / -1 = flag (x == -1) *)
    let udiv_neg_one = [
      udiv `i8 x (i8 (-1)) => flag `i8 (eq `i8 x (i8 (-1)));
      udiv `i16 x (i16 (-1)) => flag `i16 (eq `i16 x (i16 (-1)));
      udiv `i32 x (i32 (-1l)) => flag `i32 (eq `i32 x (i32 (-1l)));
      udiv `i64 x (i64 (-1L)) => flag `i64 (eq `i64 x (i64 (-1L)));
    ]

    (* unsigned x % -1 = (x != -1) ? x : 0 *)
    let urem_neg_one = [
      urem `i8 x (i8 (-1)) => sel `i8 (ne `i8 x (i8 (-1))) x (i8 0);
      urem `i16 x (i16 (-1)) => sel `i16 (ne `i16 x (i16 (-1))) x (i16 0);
      urem `i32 x (i32 (-1l)) => sel `i32 (ne `i32 x (i32 (-1l))) x (i32 0l);
      urem `i64 x (i64 (-1L)) => sel `i64 (ne `i64 x (i64 (-1L))) x (i64 0L);
    ]

    (* x % 1 = 0 *)
    let rem_one = [
      rem `i8 x (i8 1) => i8 0;
      rem `i16 x (i16 1) => i16 0;
      rem `i32 x (i32 1l) => i32 0l;
      rem `i64 x (i64 1L) => i64 0L;
      urem `i8 x (i8 1) => i8 0;
      urem `i16 x (i16 1) => i16 0;
      urem `i32 x (i32 1l) => i32 0l;
      urem `i64 x (i64 1L) => i64 0L;
    ]

    (* x & 0 = 0 *)
    let and_zero = [
      and_ `i8 x (i8 0) => i8 0;
      and_ `i16 x (i16 0) => i16 0;
      and_ `i32 x (i32 0l) => i32 0l;
      and_ `i64 x (i64 0L) => i64 0L;
    ]

    (* x & 0xff... = x *)
    let and_ones = [
      and_ `i8 x  (i8 0xff) => x;
      and_ `i16 x (i16 0xffff) => x;
      and_ `i32 x (i32 0xffff_ffffl) => x;
      and_ `i64 x (i64 0xffff_ffff_ffff_ffffL) => x;
    ]

    (* x & x = x *)
    let and_self = [
      and_ `i8 x x => x;
      and_ `i16 x x => x;
      and_ `i32 x x => x;
      and_ `i64 x x => x;
    ]

    (* x | 0 = x *)
    let or_zero = [
      or_ `i8 x (i8 0) => x;
      or_ `i16 x (i16 0) => x;
      or_ `i32 x (i32 0l) => x;
      or_ `i64 x (i64 0L) => x;
    ]

    (* x | 0xff... = 0xff... *)
    let or_ones = [
      or_ `i8 x (i8 0xff) => i8 0xff;
      or_ `i16 x (i16 0xffff) => i16 0xffff;
      or_ `i32 x (i32 0xffff_ffffl) => i32 0xffff_ffffl;
      or_ `i64 x (i64 0xffff_ffff_ffff_ffffL) => i64 0xffff_ffff_ffff_ffffL;
    ]

    (* x | x = x *)
    let or_self = [
      or_ `i8 x x => x;
      or_ `i16 x x => x;
      or_ `i32 x x => x;
      or_ `i64 x x => x;
    ]

    (* x | ~x = ~x | x = 0xff... *)
    let or_not_self = [
      or_ `i8 x (not_ `i8 x) => i8 0xff;
      or_ `i16 x (not_ `i16 x) => i16 0xffff;
      or_ `i32 x (not_ `i32 x) => i32 0xffff_ffffl;
      or_ `i64 x (not_ `i64 x) => i64 0xffff_ffff_ffff_ffffL;
      or_ `i8 (not_ `i8 x) x => i8 0xff;
      or_ `i16 (not_ `i16 x) x => i16 0xffff;
      or_ `i32 (not_ `i32 x) x => i32 0xffff_ffffl;
      or_ `i64 (not_ `i64 x) x => i64 0xffff_ffff_ffff_ffffL;
    ]

    (* ~(x | y) = ~x & ~y *)
    let demorgan_not_or = [
      not_ `i8 (or_ `i8 x y) => and_ `i8 (not_ `i8 x) (not_ `i8 y);
      not_ `i16 (or_ `i16 x y) => and_ `i16 (not_ `i16 x) (not_ `i16 y);
      not_ `i32 (or_ `i32 x y) => and_ `i32 (not_ `i32 x) (not_ `i32 y);
      not_ `i64 (or_ `i64 x y) => and_ `i64 (not_ `i64 x) (not_ `i64 y);
    ]

    (* ~(x & y) = ~x | ~y *)
    let demorgan_not_and = [
      not_ `i8 (and_ `i8 x y) => or_ `i8 (not_ `i8 x) (not_ `i8 y);
      not_ `i16 (and_ `i16 x y) => or_ `i16 (not_ `i16 x) (not_ `i16 y);
      not_ `i32 (and_ `i32 x y) => or_ `i32 (not_ `i32 x) (not_ `i32 y);
      not_ `i64 (and_ `i64 x y) => or_ `i64 (not_ `i64 x) (not_ `i64 y);
    ]

    (* (x & y) | ~y = ~y | (x & y) = x | ~y *)
    let or_and_not = [
      or_ `i8 (and_ `i8 x y) (not_ `i8 y) => or_ `i8 x (not_ `i8 y);
      or_ `i16 (and_ `i16 x y) (not_ `i16 y) => or_ `i16 x (not_ `i16 y);
      or_ `i32 (and_ `i32 x y) (not_ `i32 y) => or_ `i32 x (not_ `i32 y);
      or_ `i64 (and_ `i64 x y) (not_ `i64 y) => or_ `i64 x (not_ `i64 y);
      or_ `i8 (not_ `i8 y) (and_ `i8 x y) => or_ `i8 x (not_ `i8 y);
      or_ `i16 (not_ `i16 y) (and_ `i16 x y) => or_ `i16 x (not_ `i16 y);
      or_ `i32 (not_ `i32 y) (and_ `i32 x y) => or_ `i32 x (not_ `i32 y);
      or_ `i64 (not_ `i64 y) (and_ `i64 x y) => or_ `i64 x (not_ `i64 y);
    ]

    (* x >>> 0 = x *)
    let asr_zero = [
      asr_ `i8 x (i8 0) => x;
      asr_ `i16 x (i16 0) => x;
      asr_ `i32 x (i32 0l) => x;
      asr_ `i64 x (i64 0L) => x;
    ]

    (* x << 0 = x *)
    let lsl_zero = [
      lsl_ `i8 x (i8 0) => x;
      lsl_ `i16 x (i16 0) => x;
      lsl_ `i32 x (i32 0l) => x;
      lsl_ `i64 x (i64 0L) => x;
    ]

    (* x >> 0 = x *)
    let lsr_zero = [
      lsr_ `i8 x (i8 0) => x;
      lsr_ `i16 x (i16 0) => x;
      lsr_ `i32 x (i32 0l) => x;
      lsr_ `i64 x (i64 0L) => x;
    ]

    (* rol x 0 = x *)
    let rol_zero = [
      rol `i8 x (i8 0) => x;
      rol `i16 x (i16 0) => x;
      rol `i32 x (i32 0l) => x;
      rol `i64 x (i64 0L) => x;
    ]

    (* ror x 0 = x *)
    let ror_zero = [
      ror `i8 x (i8 0) => x;
      ror `i16 x (i16 0) => x;
      ror `i32 x (i32 0l) => x;
      ror `i64 x (i64 0L) => x;
    ]

    (* (x << y) | (x >> z) =
       (x >> z) | (x << y) =
       (x << y) + (x >> z) =
       (x >> z) + (x << y) = rol x y

       when y and z are known consts and z = size - y
    *)
    let recognize_rol_const = [
      (or_ `i8 (lsl_ `i8 x y) (lsr_ `i8 x z) =>? rol `i8 x y) ~if_:is_rotate_const_y_z;
      (or_ `i16 (lsl_ `i16 x y) (lsr_ `i16 x z) =>? rol `i16 x y) ~if_:is_rotate_const_y_z;
      (or_ `i32 (lsl_ `i32 x y) (lsr_ `i32 x z) =>? rol `i32 x y) ~if_:is_rotate_const_y_z;
      (or_ `i64 (lsl_ `i64 x y) (lsr_ `i64 x z) =>? rol `i64 x y) ~if_:is_rotate_const_y_z;
      (or_ `i8 (lsr_ `i8 x z) (lsl_ `i8 x y) =>? rol `i8 x y) ~if_:is_rotate_const_y_z;
      (or_ `i16 (lsr_ `i16 x z) (lsl_ `i16 x y) =>? rol `i16 x y) ~if_:is_rotate_const_y_z;
      (or_ `i32 (lsr_ `i32 x z) (lsl_ `i32 x y) =>? rol `i32 x y) ~if_:is_rotate_const_y_z;
      (or_ `i64 (lsr_ `i64 x z) (lsl_ `i64 x y) =>? rol `i64 x y) ~if_:is_rotate_const_y_z;
      (add `i8 (lsl_ `i8 x y) (lsr_ `i8 x z) =>? rol `i8 x y) ~if_:is_rotate_const_y_z;
      (add `i16 (lsl_ `i16 x y) (lsr_ `i16 x z) =>? rol `i16 x y) ~if_:is_rotate_const_y_z;
      (add `i32 (lsl_ `i32 x y) (lsr_ `i32 x z) =>? rol `i32 x y) ~if_:is_rotate_const_y_z;
      (add `i64 (lsl_ `i64 x y) (lsr_ `i64 x z) =>? rol `i64 x y) ~if_:is_rotate_const_y_z;
      (add `i8 (lsr_ `i8 x z) (lsl_ `i8 x y) =>? rol `i8 x y) ~if_:is_rotate_const_y_z;
      (add `i16 (lsr_ `i16 x z) (lsl_ `i16 x y) =>? rol `i16 x y) ~if_:is_rotate_const_y_z;
      (add `i32 (lsr_ `i32 x z) (lsl_ `i32 x y) =>? rol `i32 x y) ~if_:is_rotate_const_y_z;
      (add `i64 (lsr_ `i64 x z) (lsl_ `i64 x y) =>? rol `i64 x y) ~if_:is_rotate_const_y_z;
    ]

    (* (x >> y) | (x << z) =
       (x << z) | (x >> y) =
       (x >> y) + (x << z) =
       (x << z) + (x >> y) = ror x y

       when y and z are known consts and z = size - y
    *)
    let recognize_ror_const = [
      (or_ `i8 (lsr_ `i8 x y) (lsl_ `i8 x z) =>? ror `i8 x y) ~if_:is_rotate_const_y_z;
      (or_ `i16 (lsr_ `i16 x y) (lsl_ `i16 x z) =>? ror`i16 x y) ~if_:is_rotate_const_y_z;
      (or_ `i32 (lsr_ `i32 x y) (lsl_ `i32 x z) =>? ror `i32 x y) ~if_:is_rotate_const_y_z;
      (or_ `i64 (lsr_ `i64 x y) (lsl_ `i64 x z) =>? ror `i64 x y) ~if_:is_rotate_const_y_z;
      (or_ `i8 (lsl_ `i8 x z) (lsr_ `i8 x y) =>? ror `i8 x y) ~if_:is_rotate_const_y_z;
      (or_ `i16 (lsl_ `i16 x z) (lsr_ `i16 x y) =>? ror `i16 x y) ~if_:is_rotate_const_y_z;
      (or_ `i32 (lsl_ `i32 x z) (lsr_ `i32 x y) =>? ror `i32 x y) ~if_:is_rotate_const_y_z;
      (or_ `i64 (lsl_ `i64 x z) (lsr_ `i64 x y) =>? ror `i64 x y) ~if_:is_rotate_const_y_z;
      (add `i8 (lsr_ `i8 x y) (lsl_ `i8 x z) =>? ror `i8 x y) ~if_:is_rotate_const_y_z;
      (add `i16 (lsr_ `i16 x y) (lsl_ `i16 x z) =>? ror`i16 x y) ~if_:is_rotate_const_y_z;
      (add `i32 (lsr_ `i32 x y) (lsl_ `i32 x z) =>? ror `i32 x y) ~if_:is_rotate_const_y_z;
      (add `i64 (lsr_ `i64 x y) (lsl_ `i64 x z) =>? ror `i64 x y) ~if_:is_rotate_const_y_z;
      (add `i8 (lsl_ `i8 x z) (lsr_ `i8 x y) =>? ror `i8 x y) ~if_:is_rotate_const_y_z;
      (add `i16 (lsl_ `i16 x z) (lsr_ `i16 x y) =>? ror `i16 x y) ~if_:is_rotate_const_y_z;
      (add `i32 (lsl_ `i32 x z) (lsr_ `i32 x y) =>? ror `i32 x y) ~if_:is_rotate_const_y_z;
      (add `i64 (lsl_ `i64 x z) (lsr_ `i64 x y) =>? ror `i64 x y) ~if_:is_rotate_const_y_z;
    ]

    (* x ^ 0 = x *)
    let xor_zero = [
      xor `i8 x (i8 0) => x;
      xor `i16 x (i16 0) => x;
      xor `i32 x (i32 0l) => x;
      xor `i64 x (i64 0L) => x;
    ]

    (* x ^ 0xff... = ~x *)
    let xor_ones = [
      xor `i8 x (i8 0xff) => not_ `i8 x;
      xor `i16 x (i16 0xffff) => not_ `i16 x;
      xor `i32 x (i32 0xffff_ffffl) => not_ `i32 x;
      xor `i64 x (i64 0xffff_ffff_ffff_ffffL) => not_ `i64 x;
    ]

    (* x ^ x = 0 *)
    let xor_self = [
      xor `i8 x x => i8 0;
      xor `i16 x x => i16 0;
      xor `i32 x x => i32 0l;
      xor `i64 x x => i64 0L;
    ]

    (* x ^ ~x = ~x ^ x = 0xff... *)
    let xor_not_self = [
      xor `i8 x (not_ `i8 x) => i8 0xff;
      xor `i16 x (not_ `i16 x) => i16 0xffff;
      xor `i32 x (not_ `i32 x) => i32 0xffff_ffffl;
      xor `i64 x (not_ `i64 x) => i64 0xffff_ffff_ffff_ffffL;
      xor `i8 (not_ `i8 x) x => i8 0xff;
      xor `i16 (not_ `i16 x) x => i16 0xffff;
      xor `i32 (not_ `i32 x) x => i32 0xffff_ffffl;
      xor `i64 (not_ `i64 x) x => i64 0xffff_ffff_ffff_ffffL;
    ]

    (* (x ^ y) ^ y = x *)
    let double_xor = [
      xor `i8 (xor `i8 x y) y => x;
      xor `i16 (xor `i16 x y) y => x;
      xor `i32 (xor `i32 x y) y => x;
      xor `i64 (xor `i64 x y) y => x;
    ]

    (* (x >>> y) >> z = x >> z when z >= y and z is bitwidth - 1 *)
    let lsr_asr_bitwidth = [
      (lsr_ `i8 (asr_ `i8 x y) z =>? (lsr_ `i8 x z)) ~if_:lsr_asr_bitwidth_y_z;
      (lsr_ `i16 (asr_ `i16 x y) z =>? (lsr_ `i16 x z)) ~if_:lsr_asr_bitwidth_y_z;
      (lsr_ `i32 (asr_ `i32 x y) z =>? (lsr_ `i32 x z)) ~if_:lsr_asr_bitwidth_y_z;
      (lsr_ `i64 (asr_ `i64 x y) z =>? (lsr_ `i64 x z)) ~if_:lsr_asr_bitwidth_y_z;
    ]

    (* x == x = true *)
    let eq_self = [
      eq `i8 x x => bool true;
      eq `i16 x x => bool true;
      eq `i32 x x => bool true;
      eq `i64 x x => bool true;
    ]

    (* x != x = false *)
    let ne_self = [
      ne `i8 x x => bool false;
      ne `i16 x x => bool false;
      ne `i32 x x => bool false;
      ne `i64 x x => bool false;
    ]

    (* x >= x = true *)
    let ge_self = [
      ge `i8 x x => bool true;
      ge `i16 x x => bool true;
      ge `i32 x x => bool true;
      ge `i64 x x => bool true;
      sge `i8 x x => bool true;
      sge `i16 x x => bool true;
      sge `i32 x x => bool true;
      sge `i64 x x => bool true;
    ]

    (* x > x = false *)
    let gt_self = [
      gt `i8 x x => bool false;
      gt `i16 x x => bool false;
      gt `i32 x x => bool false;
      gt `i64 x x => bool false;
      sgt `i8 x x => bool false;
      sgt `i16 x x => bool false;
      sgt `i32 x x => bool false;
      sgt `i64 x x => bool false;
    ]

    (* x <= x = true *)
    let le_self = [
      le `i8 x x => bool true;
      le `i16 x x => bool true;
      le `i32 x x => bool true;
      le `i64 x x => bool true;
      sle `i8 x x => bool true;
      sle `i16 x x => bool true;
      sle `i32 x x => bool true;
      sle `i64 x x => bool true;
    ]

    (* x < x = false *)
    let lt_self = [
      lt `i8 x x => bool false;
      lt `i16 x x => bool false;
      lt `i32 x x => bool false;
      lt `i64 x x => bool false;
      slt `i8 x x => bool false;
      slt `i16 x x => bool false;
      slt `i32 x x => bool false;
      slt `i64 x x => bool false;
    ]

    (* flag (x == y) ^ 1 = flag (x != y) *)
    let xor_flag_eq_one = [
      xor `i8 (flag `i8 (eq `i8 x y)) (i8 1) => flag `i8 (ne `i8 x y);
      xor `i16 (flag `i16 (eq `i16 x y)) (i16 1) => flag `i16 (ne `i16 x y);
      xor `i32 (flag `i32 (eq `i32 x y)) (i32 1l) => flag `i32 (ne `i32 x y);
      xor `i64 (flag `i64 (eq `i64 x y)) (i64 1L) => flag `i64 (ne `i64 x y);
    ]

    (* flag (x != y) ^ 1 = flag (x == y) *)
    let xor_flag_ne_one = [
      xor `i8 (flag `i8 (ne `i8 x y)) (i8 1) => flag `i8 (eq `i8 x y);
      xor `i16 (flag `i16 (ne `i16 x y)) (i16 1) => flag `i16 (eq `i16 x y);
      xor `i32 (flag `i32 (ne `i32 x y)) (i32 1l) => flag `i32 (eq `i32 x y);
      xor `i64 (flag `i64 (ne `i64 x y)) (i64 1L) => flag `i64 (eq `i64 x y);
    ]

    (* flag (x >= y) ^ 1 = flag (x < y) *)
    let xor_flag_ge_one = [
      xor `i8 (flag `i8 (ge `i8 x y)) (i8 1) => flag `i8 (lt `i8 x y);
      xor `i16 (flag `i16 (ge `i16 x y)) (i16 1) => flag `i16 (lt `i16 x y);
      xor `i32 (flag `i32 (ge `i32 x y)) (i32 1l) => flag `i32 (lt `i32 x y);
      xor `i64 (flag `i64 (ge `i64 x y)) (i64 1L) => flag `i64 (lt `i64 x y);
      xor `i8 (flag `i8 (sge `i8 x y)) (i8 1) => flag `i8 (slt `i8 x y);
      xor `i16 (flag `i16 (sge `i16 x y)) (i16 1) => flag `i16 (slt `i16 x y);
      xor `i32 (flag `i32 (sge `i32 x y)) (i32 1l) => flag `i32 (slt `i32 x y);
      xor `i64 (flag `i64 (sge `i64 x y)) (i64 1L) => flag `i64 (slt `i64 x y);
    ]

    (* flag (x > y) ^ 1 = flag (x <= y) *)
    let xor_flag_gt_one = [
      xor `i8 (flag `i8 (gt `i8 x y)) (i8 1) => flag `i8 (le `i8 x y);
      xor `i16 (flag `i16 (gt `i16 x y)) (i16 1) => flag `i16 (le `i16 x y);
      xor `i32 (flag `i32 (gt `i32 x y)) (i32 1l) => flag `i32 (le `i32 x y);
      xor `i64 (flag `i64 (gt `i64 x y)) (i64 1L) => flag `i64 (le `i64 x y);
      xor `i8 (flag `i8 (sgt `i8 x y)) (i8 1) => flag `i8 (sle `i8 x y);
      xor `i16 (flag `i16 (sgt `i16 x y)) (i16 1) => flag `i16 (sle `i16 x y);
      xor `i32 (flag `i32 (sgt `i32 x y)) (i32 1l) => flag `i32 (sle `i32 x y);
      xor `i64 (flag `i64 (sgt `i64 x y)) (i64 1L) => flag `i64 (sle `i64 x y);
    ]

    (* flag (x <= y) ^ 1 = flag (x > y) *)
    let xor_flag_le_one = [
      xor `i8 (flag `i8 (le `i8 x y)) (i8 1) => flag `i8 (gt `i8 x y);
      xor `i16 (flag `i16 (le `i16 x y)) (i16 1) => flag `i16 (gt `i16 x y);
      xor `i32 (flag `i32 (le `i32 x y)) (i32 1l) => flag `i32 (gt `i32 x y);
      xor `i64 (flag `i64 (le `i64 x y)) (i64 1L) => flag `i64 (gt `i64 x y);
      xor `i8 (flag `i8 (sle `i8 x y)) (i8 1) => flag `i8 (sgt `i8 x y);
      xor `i16 (flag `i16 (sle `i16 x y)) (i16 1) => flag `i16 (sgt `i16 x y);
      xor `i32 (flag `i32 (sle `i32 x y)) (i32 1l) => flag `i32 (sgt `i32 x y);
      xor `i64 (flag `i64 (sle `i64 x y)) (i64 1L) => flag `i64 (sgt `i64 x y);
    ]

    (* flag (x < y) ^ 1 = flag (x >= y) *)
    let xor_flag_lt_one = [
      xor `i8 (flag `i8 (lt `i8 x y)) (i8 1) => flag `i8 (ge `i8 x y);
      xor `i16 (flag `i16 (lt `i16 x y)) (i16 1) => flag `i16 (ge `i16 x y);
      xor `i32 (flag `i32 (lt `i32 x y)) (i32 1l) => flag `i32 (ge `i32 x y);
      xor `i64 (flag `i64 (lt `i64 x y)) (i64 1L) => flag `i64 (ge `i64 x y);
      xor `i8 (flag `i8 (slt `i8 x y)) (i8 1) => flag `i8 (sge `i8 x y);
      xor `i16 (flag `i16 (slt `i16 x y)) (i16 1) => flag `i16 (sge `i16 x y);
      xor `i32 (flag `i32 (slt `i32 x y)) (i32 1l) => flag `i32 (sge `i32 x y);
      xor `i64 (flag `i64 (slt `i64 x y)) (i64 1L) => flag `i64 (sge `i64 x y);
    ]

    (* unsigned x < 0 = false *)
    let ult_zero = [
      lt `i8 x (i8 0) => bool false;
      lt `i16 x (i16 0) => bool false;
      lt `i32 x (i32 0l) => bool false;
      lt `i64 x (i64 0L) => bool false;
    ]

    (* unsigned x >= 0 = true *)
    let uge_zero = [
      ge `i8 x (i8 0) => bool true;
      ge `i16 x (i16 0) => bool true;
      ge `i32 x (i32 0l) => bool true;
      ge `i64 x (i64 0L) => bool true;
    ]

    (* unsigned x <= 0 = x == 0 *)
    let ule_zero = [
      le `i8 x (i8 0) => eq `i8 x (i8 0);
      le `i16 x (i16 0) => eq `i16 x (i16 0);
      le `i32 x (i32 0l) => eq `i32 x (i32 0l);
      le `i64 x (i64 0L) => eq `i64 x (i64 0L);
    ]

    (* unsigned x > 0 = x != 0 *)
    let ugt_zero = [
      gt `i8 x (i8 0) => ne `i8 x (i8 0);
      gt `i16 x (i16 0) => ne `i16 x (i16 0);
      gt `i32 x (i32 0l) => ne `i32 x (i32 0l);
      gt `i64 x (i64 0L) => ne `i64 x (i64 0L);
    ]

    (* unsigned x < 0xff... = x != 0xff... *)
    let ult_ones = [
      lt `i8 x (i8 0xff) => ne `i8 x (i8 0xff);
      lt `i16 x (i16 0xffff) => ne `i16 x (i16 0xffff);
      lt `i32 x (i32 0xffff_ffffl) => ne `i32 x (i32 0xffff_ffffl);
      lt `i64 x (i64 0xffff_ffff_ffff_ffffL) => ne `i64 x (i64 0xffff_ffff_ffff_ffffL);
    ]

    (* unsigned x >= 0xff... = x == 0xff... *)
    let uge_ones = [
      ge `i8 x (i8 0xff) => eq `i8 x (i8 0xff);
      ge `i16 x (i16 0xffff) => eq `i16 x (i16 0xffff);
      ge `i32 x (i32 0xffff_ffffl) => eq `i32 x (i32 0xffff_ffffl);
      ge `i64 x (i64 0xffff_ffff_ffff_ffffL) => eq `i64 x (i64 0xffff_ffff_ffff_ffffL);
    ]

    (* unsigned x <= 0xff... = true *)
    let ule_ones = [
      le `i8 x (i8 0xff) => bool true;
      le `i16 x (i16 0xffff) => bool true;
      le `i32 x (i32 0xffff_ffffl) => bool true;
      le `i64 x (i64 0xffff_ffff_ffff_ffffL) => bool true;
    ]

    (* unsigned x > 0xff... = false *)
    let ugt_ones = [
      gt `i8 x (i8 0xff) => bool false;
      gt `i16 x (i16 0xffff) => bool false;
      gt `i32 x (i32 0xffff_ffffl) => bool false;
      gt `i64 x (i64 0xffff_ffff_ffff_ffffL) => bool false;
    ]

    (* signed x < 0x80... = false *)
    let slt_min = [
      slt `i8 x (i8 0x80) => bool false;
      slt `i16 x (i16 0x8000) => bool false;
      slt `i32 x (i32 0x8000_0000l) => bool false;
      slt `i64 x (i64 0x8000_0000_0000_0000L) => bool false;
    ]

    (* signed x >= 0x80... = true *)
    let sge_min = [
      sge `i8 x (i8 0x80) => bool true;
      sge `i16 x (i16 0x8000) => bool true;
      sge `i32 x (i32 0x8000_0000l) => bool true;
      sge `i64 x (i64 0x8000_0000_0000_0000L) => bool true;
    ]

    (* signed x <= 0x80... = x == 0x80... *)
    let sle_min = [
      sle `i8 x (i8 0x80) => eq `i8 x (i8 0x80);
      sle `i16 x (i16 0x8000) => eq `i16 x (i16 0x8000);
      sle `i32 x (i32 0x8000_0000l) => eq `i32 x (i32 0x8000_0000l);
      sle `i64 x (i64 0x8000_0000_0000_0000L) => eq `i64 x (i64 0x8000_0000_0000_0000L);
    ]

    (* signed x > 0x80... = x != 0x80... *)
    let sgt_min = [
      sgt `i8 x (i8 0x80) => ne `i8 x (i8 0x80);
      sgt `i16 x (i16 0x8000) => ne `i16 x (i16 0x8000);
      sgt `i32 x (i32 0x8000_0000l) => ne `i32 x (i32 0x8000_0000l);
      sgt `i64 x (i64 0x8000_0000_0000_0000L) => ne `i64 x (i64 0x8000_0000_0000_0000L);
    ]

    (* signed x > 0x7f... = false *)
    let sgt_max = [
      sgt `i8 x (i8 0x7f) => bool false;
      sgt `i16 x (i16 0x7fff) => bool false;
      sgt `i32 x (i32 0x7fff_ffffl) => bool false;
      sgt `i64 x (i64 0x7fff_ffff_ffff_ffffL) => bool false;
    ]

    (* signed x <= 0x7f... = true *)
    let sle_max = [
      sle `i8 x (i8 0x7f) => bool true;
      sle `i16 x (i16 0x7fff) => bool true;
      sle `i32 x (i32 0x7fff_ffffl) => bool true;
      sle `i64 x (i64 0x7fff_ffff_ffff_ffffL) => bool true;
    ]

    (* signed x >= 0x7f... = x == 0x7f... *)
    let sge_max = [
      sge `i8 x (i8 0x7f) => eq `i8 x (i8 0x7f);
      sge `i16 x (i16 0x7fff) => eq `i16 x (i16 0x7fff);
      sge `i32 x (i32 0x7fff_ffffl) => eq `i32 x (i32 0x7fff_ffffl);
      sge `i64 x (i64 0x7fff_ffff_ffff_ffffL) => eq `i64 x (i64 0x7fff_ffff_ffff_ffffL);
    ]

    (* signed x < 0x7f... = x != 0x7f... *)
    let slt_max = [
      slt `i8 x (i8 0x7f) => ne `i8 x (i8 0x7f);
      slt `i16 x (i16 0x7fff) => ne `i16 x (i16 0x7fff);
      slt `i32 x (i32 0x7fff_ffffl) => ne `i32 x (i32 0x7fff_ffffl);
      slt `i64 x (i64 0x7fff_ffff_ffff_ffffL) => ne `i64 x (i64 0x7fff_ffff_ffff_ffffL);
    ]

    (* signed (zext x) < 0 = false when x has a smaller type *)
    let slt_zero_zext = [
      (slt `i16 (zext `i16 x) (i16 0) =>? bool false) ~if_:(has_type_x `i8);
      (slt `i32 (zext `i32 x) (i32 0l) =>? bool false) ~if_:(has_type_x `i8);
      (slt `i32 (zext `i32 x) (i32 0l) =>? bool false) ~if_:(has_type_x `i16);
      (slt `i64 (zext `i64 x) (i64 0L) =>? bool false) ~if_:(has_type_x `i8);
      (slt `i64 (zext `i64 x) (i64 0L) =>? bool false) ~if_:(has_type_x `i16);
      (slt `i64 (zext `i64 x) (i64 0L) =>? bool false) ~if_:(has_type_x `i32);
    ]

    (* signed (zext x) >= 0 = true when x has a smaller type *)
    let sge_zero_zext = [
      (sge `i16 (zext `i16 x) (i16 0) =>? bool true) ~if_:(has_type_x `i8);
      (sge `i32 (zext `i32 x) (i32 0l) =>? bool true) ~if_:(has_type_x `i8);
      (sge `i32 (zext `i32 x) (i32 0l) =>? bool true) ~if_:(has_type_x `i16);
      (sge `i64 (zext `i64 x) (i64 0L) =>? bool true) ~if_:(has_type_x `i8);
      (sge `i64 (zext `i64 x) (i64 0L) =>? bool true) ~if_:(has_type_x `i16);
      (sge `i64 (zext `i64 x) (i64 0L) =>? bool true) ~if_:(has_type_x `i32);
    ]

    (* flag x == 1 = x *)
    let flag_eq_one = [
      eq `i8 (flag `i8 x) (i8 1) => x;
      eq `i16 (flag `i16 x) (i16 1) => x;
      eq `i32 (flag `i32 x) (i32 1l) => x;
      eq `i64 (flag `i64 x) (i64 1L) => x;
    ]

    (* flag x == 0 = (flag x ^ 1) == 1 *)
    let flag_eq_zero = [
      eq `i8 (flag `i8 x) (i8 0) => eq `i8 (xor `i8 (flag `i8 x) (i8 1)) (i8 1);
      eq `i16 (flag `i16 x) (i16 0) => eq `i16 (xor `i16 (flag `i16 x) (i16 1)) (i16 1);
      eq `i32 (flag `i32 x) (i32 0l) => eq `i32 (xor `i32 (flag `i32 x) (i32 1l)) (i32 1l);
      eq `i64 (flag `i64 x) (i64 0L) => eq `i64 (xor `i64 (flag `i64 x) (i64 1L)) (i64 1L);
    ]

    (* flag x != 1 = flag == 0 *)
    let flag_ne_one = [
      ne `i8 (flag `i8 x) (i8 1) => eq `i8 (flag `i8 x) (i8 0);
      ne `i16 (flag `i16 x) (i16 1) => eq `i16 (flag `i16 x) (i16 0);
      ne `i32 (flag `i32 x) (i32 1l) => eq `i32 (flag `i32 x) (i32 0l);
      ne `i64 (flag `i64 x) (i64 1L) => eq `i64 (flag `i64 x) (i64 0L);
    ]

    (* flag x != 0 = x *)
    let flag_ne_zero = [
      ne `i8 (flag `i8 x) (i8 0) => x;
      ne `i16 (flag `i16 x) (i16 0) => x;
      ne `i32 (flag `i32 x) (i32 0l) => x;
      ne `i64 (flag `i64 x) (i64 0L) => x;
    ]

    (* unsigned flag x <= 0 = flag x == 0 *)
    let flag_ule_zero = [
      le `i8 (flag `i8 x) (i8 0) => eq `i8 (flag `i8 x) (i8 0);
      le `i16 (flag `i16 x) (i16 0) => eq `i16 (flag `i16 x) (i16 0);
      le `i32 (flag `i32 x) (i32 0l) => eq `i32 (flag `i32 x) (i32 0l);
      le `i64 (flag `i64 x) (i64 0L) => eq `i64 (flag `i64 x) (i64 0L);
    ]

    (* unsigned flag x <= 1 = true *)
    let flag_ule_one = [
      le `i8 (flag `i8 x) (i8 1) => bool true;
      le `i16 (flag `i16 x) (i16 1) => bool true;
      le `i32 (flag `i32 x) (i32 1l) => bool true;
      le `i64 (flag `i64 x) (i64 1L) => bool true;
    ]

    (* signed flag x <= 1 = true *)
    let flag_sle_one = [
      sle `i8 (flag `i8 x) (i8 1) => bool true;
      sle `i16 (flag `i16 x) (i16 1) => bool true;
      sle `i32 (flag `i32 x) (i32 1l) => bool true;
      sle `i64 (flag `i64 x) (i64 1L) => bool true;
    ]

    (* signed flag x <= 0 = flag x == 0 *)
    let flag_sle_zero = [
      sle `i8 (flag `i8 x) (i8 0) => eq `i8 (flag `i8 x) (i8 0);
      sle `i16 (flag `i16 x) (i16 0) => eq `i16 (flag `i16 x) (i16 0);
      sle `i32 (flag `i32 x) (i32 0l) => eq `i32 (flag `i32 x) (i32 0l);
      sle `i64 (flag `i64 x) (i64 0L) => eq `i64 (flag `i64 x) (i64 0L);
    ]

    (* unsigned flag x < 1 = flag x == 0 *)
    let flag_ult_one = [
      lt `i8 (flag `i8 x) (i8 1) => eq `i8 (flag `i8 x) (i8 0);
      lt `i16 (flag `i16 x) (i16 1) => eq `i16 (flag `i16 x) (i16 0);
      lt `i32 (flag `i32 x) (i32 1l) => eq `i32 (flag `i32 x) (i32 0l);
      lt `i64 (flag `i64 x) (i64 1L) => eq `i64 (flag `i64 x) (i64 0L);
    ]

    (* signed flag < 1 = flag x == 0 *)
    let flag_slt_one = [
      slt `i8 (flag `i8 x) (i8 1) => eq `i8 (flag `i8 x) (i8 0);
      slt `i16 (flag `i16 x) (i16 1) => eq `i16 (flag `i16 x) (i16 0);
      slt `i32 (flag `i32 x) (i32 1l) => eq `i32 (flag `i32 x) (i32 0l);
      slt `i64 (flag `i64 x) (i64 1L) => eq `i64 (flag `i64 x) (i64 0L);
    ]

    (* unsigned flag x < 0 = false *)
    let flag_ult_zero = [
      lt `i8 (flag `i8 x) (i8 0) => bool false;
      lt `i16 (flag `i16 x) (i16 0) => bool false;
      lt `i32 (flag `i32 x) (i32 0l) => bool false;
      lt `i64 (flag `i64 x) (i64 0L) => bool false;
    ]

    (* signed flag x < 0 = false *)
    let flag_slt_zero = [
      slt `i8 (flag `i8 x) (i8 0) => bool false;
      slt `i16 (flag `i16 x) (i16 0) => bool false;
      slt `i32 (flag `i32 x) (i32 0l) => bool false;
      slt `i64 (flag `i64 x) (i64 0L) => bool false;
    ]

    (* unsigned flag x >= 0 = true *)
    let flag_uge_zero = [
      ge `i8 (flag `i8 x) (i8 0) => bool true;
      ge `i16 (flag `i16 x) (i16 0) => bool true;
      ge `i32 (flag `i32 x) (i32 0l) => bool true;
      ge `i64 (flag `i64 x) (i64 0L) => bool true;
    ]

    (* signed flag >= 0 = true *)
    let flag_sge_zero = [
      sge `i8 (flag `i8 x) (i8 0) => bool true;
      sge `i16 (flag `i16 x) (i16 0) => bool true;
      sge `i32 (flag `i32 x) (i32 0l) => bool true;
      sge `i64 (flag `i64 x) (i64 0L) => bool true;
    ]

    (* unsigned flag x >= 1 = flag x == 1 *)
    let flag_uge_one = [
      ge `i8 (flag `i8 x) (i8 1) => eq `i8 (flag `i8 x) (i8 1);
      ge `i16 (flag `i16 x) (i16 1) => eq `i16 (flag `i16 x) (i16 1);
      ge `i32 (flag `i32 x) (i32 1l) => eq `i32 (flag `i32 x) (i32 1l);
      ge `i64 (flag `i64 x) (i64 1L) => eq `i64 (flag `i64 x) (i64 1L);
    ]

    (* signed flag x >= 1 = flag x == 1 *)
    let flag_sge_one = [
      sge `i8 (flag `i8 x) (i8 1) => eq `i8 (flag `i8 x) (i8 1);
      sge `i16 (flag `i16 x) (i16 1) => eq `i16 (flag `i16 x) (i16 1);
      sge `i32 (flag `i32 x) (i32 1l) => eq `i32 (flag `i32 x) (i32 1l);
      sge `i64 (flag `i64 x) (i64 1L) => eq `i64 (flag `i64 x) (i64 1L);
    ]

    (* unsigned flag x > 0 = flag x == 1 *)
    let flag_ugt_zero = [
      gt `i8 (flag `i8 x) (i8 0) => eq `i8 (flag `i8 x) (i8 1);
      gt `i16 (flag `i16 x) (i16 0) => eq `i16 (flag `i16 x) (i16 1);
      gt `i32 (flag `i32 x) (i32 0l) => eq `i32 (flag `i32 x) (i32 1l);
      gt `i64 (flag `i64 x) (i64 0L) => eq `i64 (flag `i64 x) (i64 1L);
    ]

    (* signed flag x > 0 = flag x == 1 *)
    let flag_sgt_zero = [
      sgt `i8 (flag `i8 x) (i8 0) => eq `i8 (flag `i8 x) (i8 1);
      sgt `i16 (flag `i16 x) (i16 0) => eq `i16 (flag `i16 x) (i16 1);
      sgt `i32 (flag `i32 x) (i32 0l) => eq `i32 (flag `i32 x) (i32 1l);
      sgt `i64 (flag `i64 x) (i64 0L) => eq `i64 (flag `i64 x) (i64 1L);
    ]

    (* unsigned flag x > 1 = false *)
    let flag_ugt_one = [
      gt `i8 (flag `i8 x) (i8 1) => bool false;
      gt `i16 (flag `i16 x) (i16 1) => bool false;
      gt `i32 (flag `i32 x) (i32 1l) => bool false;
      gt `i64 (flag `i64 x) (i64 1L) => bool false;
    ]

    (* signed flag x > 1 = false *)
    let flag_sgt_one = [
      sgt `i8 (flag `i8 x) (i8 1) => bool false;
      sgt `i16 (flag `i16 x) (i16 1) => bool false;
      sgt `i32 (flag `i32 x) (i32 1l) => bool false;
      sgt `i64 (flag `i64 x) (i64 1L) => bool false;
    ]

    (* (flag x == y) = (y == flag x) = false when y is not 0 or 1 *)
    let flag_eq_not_bool = [
      (eq `i8 (flag `i8 x) y =>? bool false) ~if_:is_not_bool_y;
      (eq `i16 (flag `i16 x) y =>? bool false) ~if_:is_not_bool_y;
      (eq `i32 (flag `i32 x) y =>? bool false) ~if_:is_not_bool_y;
      (eq `i64 (flag `i64 x) y =>? bool false) ~if_:is_not_bool_y;
      (eq `i8 y (flag `i8 x) =>? bool false) ~if_:is_not_bool_y;
      (eq `i16 y (flag `i16 x) =>? bool false) ~if_:is_not_bool_y;
      (eq `i32 y (flag `i32 x) =>? bool false) ~if_:is_not_bool_y;
      (eq `i64 y (flag `i64 x) =>? bool false) ~if_:is_not_bool_y;
    ]

    (* (flag x != y) = (y != flag x) = true when y is not 0 or 1 *)
    let flag_ne_not_bool = [
      (ne `i8 (flag `i8 x) y =>? bool true) ~if_:is_not_bool_y;
      (ne `i16 (flag `i16 x) y =>? bool true) ~if_:is_not_bool_y;
      (ne `i32 (flag `i32 x) y =>? bool true) ~if_:is_not_bool_y;
      (ne `i64 (flag `i64 x) y =>? bool true) ~if_:is_not_bool_y;
      (ne `i8 y (flag `i8 x) =>? bool true) ~if_:is_not_bool_y;
      (ne `i16 y (flag `i16 x) =>? bool true) ~if_:is_not_bool_y;
      (ne `i32 y (flag `i32 x) =>? bool true) ~if_:is_not_bool_y;
      (ne `i64 y (flag `i64 x) =>? bool true) ~if_:is_not_bool_y;
    ]

    (* (flag x < y) = true
       (y < flag x) = false

       when y is not 0 or 1
    *)
    let flag_ult_not_bool = [
      (lt `i8 (flag `i8 x) y =>? bool true) ~if_:is_not_bool_y;
      (lt `i16 (flag `i16 x) y =>? bool true) ~if_:is_not_bool_y;
      (lt `i32 (flag `i32 x) y =>? bool true) ~if_:is_not_bool_y;
      (lt `i64 (flag `i64 x) y =>? bool true) ~if_:is_not_bool_y;
      (lt `i8 y (flag `i8 x) =>? bool false) ~if_:is_not_bool_y;
      (lt `i16 y (flag `i16 x) =>? bool false) ~if_:is_not_bool_y;
      (lt `i32 y (flag `i32 x) =>? bool false) ~if_:is_not_bool_y;
      (lt `i64 y (flag `i64 x) =>? bool false) ~if_:is_not_bool_y;
    ]

    (* (signed flag x < y) = true
       (signed y < flag x) = false

       when signed y > 1
       opposite when signed y < 0
    *)
    let flag_slt_not_bool = [
      (slt `i8 (flag `i8 x) y =>? bool true) ~if_:is_sgt_one_y;
      (slt `i16 (flag `i16 x) y =>? bool true) ~if_:is_sgt_one_y;
      (slt `i32 (flag `i32 x) y =>? bool true) ~if_:is_sgt_one_y;
      (slt `i64 (flag `i64 x) y =>? bool true) ~if_:is_sgt_one_y;
      (slt `i8 y (flag `i8 x) =>? bool false) ~if_:is_sgt_one_y;
      (slt `i16 y (flag `i16 x) =>? bool false) ~if_:is_sgt_one_y;
      (slt `i32 y (flag `i32 x) =>? bool false) ~if_:is_sgt_one_y;
      (slt `i64 y (flag `i64 x) =>? bool false) ~if_:is_sgt_one_y;
      (slt `i8 (flag `i8 x) y =>? bool false) ~if_:is_slt_zero_y;
      (slt `i16 (flag `i16 x) y =>? bool false) ~if_:is_slt_zero_y;
      (slt `i32 (flag `i32 x) y =>? bool false) ~if_:is_slt_zero_y;
      (slt `i64 (flag `i64 x) y =>? bool false) ~if_:is_slt_zero_y;
      (slt `i8 y (flag `i8 x) =>? bool true) ~if_:is_slt_zero_y;
      (slt `i16 y (flag `i16 x) =>? bool true) ~if_:is_slt_zero_y;
      (slt `i32 y (flag `i32 x) =>? bool true) ~if_:is_slt_zero_y;
      (slt `i64 y (flag `i64 x) =>? bool true) ~if_:is_slt_zero_y;
    ]

    (* (flag x <= y) = true
       (y <= flag x) = false

       when y is not 0 or 1
    *)
    let flag_ule_not_bool = [
      (le `i8 (flag `i8 x) y =>? bool true) ~if_:is_not_bool_y;
      (le `i16 (flag `i16 x) y =>? bool true) ~if_:is_not_bool_y;
      (le `i32 (flag `i32 x) y =>? bool true) ~if_:is_not_bool_y;
      (le `i64 (flag `i64 x) y =>? bool true) ~if_:is_not_bool_y;
      (le `i8 y (flag `i8 x) =>? bool false) ~if_:is_not_bool_y;
      (le `i16 y (flag `i16 x) =>? bool false) ~if_:is_not_bool_y;
      (le `i32 y (flag `i32 x) =>? bool false) ~if_:is_not_bool_y;
      (le `i64 y (flag `i64 x) =>? bool false) ~if_:is_not_bool_y;
    ]

    (* (signed flag x <= y) = true
       (signed y <= flag x) = false

       when signed y > 1
       opposite when signed y < 0
    *)
    let flag_sle_not_bool = [
      (sle `i8 (flag `i8 x) y =>? bool true) ~if_:is_sgt_one_y;
      (sle `i16 (flag `i16 x) y =>? bool true) ~if_:is_sgt_one_y;
      (sle `i32 (flag `i32 x) y =>? bool true) ~if_:is_sgt_one_y;
      (sle `i64 (flag `i64 x) y =>? bool true) ~if_:is_sgt_one_y;
      (sle `i8 x (flag `i8 x) =>? bool false) ~if_:is_sgt_one_y;
      (sle `i16 x (flag `i16 x) =>? bool false) ~if_:is_sgt_one_y;
      (sle `i32 x (flag `i32 x) =>? bool false) ~if_:is_sgt_one_y;
      (sle `i64 x (flag `i64 x) =>? bool false) ~if_:is_sgt_one_y;
      (sle `i8 (flag `i8 x) y =>? bool false) ~if_:is_slt_zero_y;
      (sle `i16 (flag `i16 x) y =>? bool false) ~if_:is_slt_zero_y;
      (sle `i32 (flag `i32 x) y =>? bool false) ~if_:is_slt_zero_y;
      (sle `i64 (flag `i64 x) y =>? bool false) ~if_:is_slt_zero_y;
      (sle `i8 x (flag `i8 x) =>? bool true) ~if_:is_slt_zero_y;
      (sle `i16 x (flag `i16 x) =>? bool true) ~if_:is_slt_zero_y;
      (sle `i32 x (flag `i32 x) =>? bool true) ~if_:is_slt_zero_y;
      (sle `i64 x (flag `i64 x) =>? bool true) ~if_:is_slt_zero_y;
    ]

    (* (flag x > y) = false
       (y > flag x) = true

       when y is not 0 or 1
    *)
    let flag_ugt_not_bool = [
      (gt `i8 (flag `i8 x) y =>? bool false) ~if_:is_not_bool_y;
      (gt `i16 (flag `i16 x) y =>? bool false) ~if_:is_not_bool_y;
      (gt `i32 (flag `i32 x) y =>? bool false) ~if_:is_not_bool_y;
      (gt `i64 (flag `i64 x) y =>? bool false) ~if_:is_not_bool_y;
      (gt `i8 y (flag `i8 x) =>? bool true) ~if_:is_not_bool_y;
      (gt `i16 y (flag `i16 x) =>? bool true) ~if_:is_not_bool_y;
      (gt `i32 y (flag `i32 x) =>? bool true) ~if_:is_not_bool_y;
      (gt `i64 y (flag `i64 x) =>? bool true) ~if_:is_not_bool_y;
    ]

    (* (signed flag x > y) = false
       (signed y > flag x) = true

       when signed y > 1
       opposite when signed y < 0
    *)
    let flag_sgt_not_bool = [
      (sgt `i8 (flag `i8 x) y =>? bool false) ~if_:is_sgt_one_y;
      (sgt `i16 (flag `i16 x) y =>? bool false) ~if_:is_sgt_one_y;
      (sgt `i32 (flag `i32 x) y =>? bool false) ~if_:is_sgt_one_y;
      (sgt `i64 (flag `i64 x) y =>? bool false) ~if_:is_sgt_one_y;
      (sgt `i8 y (flag `i8 x) =>? bool true) ~if_:is_sgt_one_y;
      (sgt `i16 y (flag `i16 x) =>? bool true) ~if_:is_sgt_one_y;
      (sgt `i32 y (flag `i32 x) =>? bool true) ~if_:is_sgt_one_y;
      (sgt `i64 y (flag `i64 x) =>? bool true) ~if_:is_sgt_one_y;
      (sgt `i8 (flag `i8 x) y =>? bool true) ~if_:is_slt_zero_y;
      (sgt `i16 (flag `i16 x) y =>? bool true) ~if_:is_slt_zero_y;
      (sgt `i32 (flag `i32 x) y =>? bool true) ~if_:is_slt_zero_y;
      (sgt `i64 (flag `i64 x) y =>? bool true) ~if_:is_slt_zero_y;
      (sgt `i8 y (flag `i8 x) =>? bool false) ~if_:is_slt_zero_y;
      (sgt `i16 y (flag `i16 x) =>? bool false) ~if_:is_slt_zero_y;
      (sgt `i32 y (flag `i32 x) =>? bool false) ~if_:is_slt_zero_y;
      (sgt `i64 y (flag `i64 x) =>? bool false) ~if_:is_slt_zero_y;
    ]

    (* (flag x >= y) = false
       (y >= flag x) = true

       when y is not 0 or 1
    *)
    let flag_uge_not_bool = [
      (ge `i8 (flag `i8 x) y =>? bool false) ~if_:is_not_bool_y;
      (ge `i16 (flag `i16 x) y =>? bool false) ~if_:is_not_bool_y;
      (ge `i32 (flag `i32 x) y =>? bool false) ~if_:is_not_bool_y;
      (ge `i64 (flag `i64 x) y =>? bool false) ~if_:is_not_bool_y;
      (ge `i8 y (flag `i8 x) =>? bool true) ~if_:is_not_bool_y;
      (ge `i16 y (flag `i16 x) =>? bool true) ~if_:is_not_bool_y;
      (ge `i32 y (flag `i32 x) =>? bool true) ~if_:is_not_bool_y;
      (ge `i64 y (flag `i64 x) =>? bool true) ~if_:is_not_bool_y;
    ]

    (* (signed flag x >= y) = false
       (signed y >= flag x) = true

       when signed y > 1
       opposite when signed y < 0
    *)
    let flag_sge_not_bool = [
      (sge `i8 (flag `i8 x) y =>? bool false) ~if_:is_sgt_one_y;
      (sge `i16 (flag `i16 x) y =>? bool false) ~if_:is_sgt_one_y;
      (sge `i32 (flag `i32 x) y =>? bool false) ~if_:is_sgt_one_y;
      (sge `i64 (flag `i64 x) y =>? bool false) ~if_:is_sgt_one_y;
      (sge `i8 y (flag `i8 x) =>? bool true) ~if_:is_sgt_one_y;
      (sge `i16 y (flag `i16 x) =>? bool true) ~if_:is_sgt_one_y;
      (sge `i32 y (flag `i32 x) =>? bool true) ~if_:is_sgt_one_y;
      (sge `i64 y (flag `i64 x) =>? bool true) ~if_:is_sgt_one_y;
      (sge `i8 (flag `i8 x) y =>? bool true) ~if_:is_slt_zero_y;
      (sge `i16 (flag `i16 x) y =>? bool true) ~if_:is_slt_zero_y;
      (sge `i32 (flag `i32 x) y =>? bool true) ~if_:is_slt_zero_y;
      (sge `i64 (flag `i64 x) y =>? bool true) ~if_:is_slt_zero_y;
      (sge `i8 y (flag `i8 x) =>? bool false) ~if_:is_slt_zero_y;
      (sge `i16 y (flag `i16 x) =>? bool false) ~if_:is_slt_zero_y;
      (sge `i32 y (flag `i32 x) =>? bool false) ~if_:is_slt_zero_y;
      (sge `i64 y (flag `i64 x) =>? bool false) ~if_:is_slt_zero_y;
    ]

    (* extend t1 (flag t2 x) = flag t1 x *)
    let extend_flag = [
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
    ]

    (* itrunc t1 (flag t2 x) = flag t1 x *)
    let trunc_flag = [
      itrunc `i8 (flag `i16 x) => flag `i8 x;
      itrunc `i8 (flag `i32 x) => flag `i8 x;
      itrunc `i8 (flag `i64 x) => flag `i8 x;
      itrunc `i16 (flag `i32 x) => flag `i16 x;
      itrunc `i16 (flag `i64 x) => flag `i16 x;
      itrunc `i32 (flag `i64 x) => flag `i32 x;
    ]

    (* extend i8 x = x *)
    let extend_i8 = [
      sext `i8 x => x;
      zext `i8 x => x;
    ]

    (* extend (extend x) = extend x *)
    let double_extend = [
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
    ]

    (* extend x to original type = x *)
    let extend_nop = [
      sext `i16 x =>* identity_same_type_x `i16;
      zext `i16 x =>* identity_same_type_x `i16;
      sext `i32 x =>* identity_same_type_x `i32;
      zext `i32 x =>* identity_same_type_x `i32;
      sext `i64 x =>* identity_same_type_x `i64;
      zext `i64 x =>* identity_same_type_x `i64;
    ]

    (* itrunc x to original type = x *)
    let itrunc_nop = [
      itrunc `i8 x =>* identity_same_type_x `i8;
      itrunc `i16 x =>* identity_same_type_x `i16;
      itrunc `i32 x =>* identity_same_type_x `i32;
      itrunc `i64 x => x;
    ]

    (* itrunc (sext/zext x) to original type = x; these are the cases
       not covered by the general case above. *)
    let itrunc_extend_nop = [
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
    ]

    (* br true, x, y = jmp x
       br false, x, y = jmp y
       br x, y, y = jmp y
    *)
    let br_const = [
      br (bool true) x y => jmp x;
      br (bool false) x y => jmp y;
      br x y y => jmp y;
    ]

    (* true ? x : y = x
       false ? x : y = y
       x ? y : y = y
    *)
    let sel_const = [
      sel `i8 (bool true) x y => x;
      sel `i16 (bool true) x y => x;
      sel `i32 (bool true) x y => x;
      sel `i64 (bool true) x y => x;
      sel `f32 (bool true) x y => x;
      sel `f64 (bool true) x y => x;
      sel `i8 (bool false) x y => y;
      sel `i16 (bool false) x y => y;
      sel `i32 (bool false) x y => y;
      sel `i64 (bool false) x y => y;
      sel `f32 (bool false) x y => y;
      sel `f64 (bool false) x y => y;
      sel `i8 x y y => y;
      sel `i16 x y y => y;
      sel `i32 x y y => y;
      sel `i64 x y y => y;
      sel `f32 x y y => y;
      sel `f64 x y y => y;
    ]

    (* Specialize `sel` to `flag` when the arms are 0 or 1 *)
    let sel_bool = [
      sel `i8 x (i8 1) (i8 0) => flag `i8 x;
      sel `i16 x (i16 1) (i16 0) => flag `i16 x;
      sel `i32 x (i32 1l) (i32 0l) => flag `i32 x;
      sel `i64 x (i64 1L) (i64 0L) => flag `i64 x;
      sel `i8 x (i8 0) (i8 1) => xor `i8 (flag `i8 x) (i8 1);
      sel `i16 x (i16 0) (i16 1) => xor `i16 (flag `i16 x) (i16 1);
      sel `i32 x (i32 0l) (i32 1l) => xor `i32 (flag `i32 x) (i32 1l);
      sel `i64 x (i64 0L) (i64 1L) => xor `i64 (flag `i64 x) (i64 1L);
    ]

    (* Copy propagation. *)
    let prop_copy = [
      copy `i8 x => x;
      copy `i16 x => x;
      copy `i32 x => x;
      copy `i64 x => x;
      copy `f32 x => x;
      copy `f64 x => x;
    ]

    (* All rules. *)
    let all =
      commute_consts @
      assoc_consts @
      add_neg_const @
      sub_neg_const @
      add_neg @
      sub_neg @
      add_zero @
      sub_zero @
      sub_zero_neg @
      double_neg @
      double_not @
      inc_not @
      mul_negs @
      sub_self @
      mul_zero @
      mul_one @
      mul_neg_one @
      mul_two_add_self @
      mul_pow2 @
      sdiv_const_pow2 @
      sdiv_const_non_pow2 @
      srem_const_pow2 @
      srem_const_non_pow2 @
      udiv_const_pow2 @
      udiv_const_non_pow2 @
      urem_const_pow2 @
      urem_const_non_pow2 @
      div_one @
      div_self @
      rem_self @
      sdiv_neg_one @
      srem_neg_one @
      udiv_neg_one @
      urem_neg_one @
      rem_one @
      and_zero @
      and_ones @
      and_self @
      or_zero @
      or_ones @
      or_self @
      or_not_self @
      demorgan_not_or @
      demorgan_not_and @
      or_and_not @
      asr_zero @
      lsl_zero @
      lsr_zero @
      rol_zero @
      ror_zero @
      recognize_rol_const @
      recognize_ror_const @
      xor_zero @
      xor_ones @
      xor_self @
      xor_not_self @
      double_xor @
      lsr_asr_bitwidth @
      eq_self @
      ne_self @
      ge_self @
      gt_self @
      le_self @
      lt_self @
      xor_flag_eq_one @
      xor_flag_ne_one @
      xor_flag_ge_one @
      xor_flag_gt_one @
      xor_flag_le_one @
      xor_flag_lt_one @
      ult_zero @
      uge_zero @
      ule_zero @
      ugt_zero @
      ult_ones @
      uge_ones @
      ule_ones @
      ugt_ones @
      slt_min @
      sge_min @
      sle_min @
      sgt_min @
      sgt_max @
      sle_max @
      sge_max @
      slt_max @
      slt_zero_zext @
      sge_zero_zext @
      flag_eq_one @
      flag_eq_zero @
      flag_ne_one @
      flag_ne_zero @
      flag_ule_zero @
      flag_ule_one @
      flag_sle_one @
      flag_sle_zero @
      flag_ult_one @
      flag_slt_one @
      flag_ult_zero @
      flag_slt_zero @
      flag_uge_zero @
      flag_sge_zero @
      flag_uge_one @
      flag_sge_one @
      flag_ugt_zero @
      flag_sgt_zero @
      flag_ugt_one @
      flag_sgt_one @
      flag_eq_not_bool @
      flag_ne_not_bool @
      flag_ult_not_bool @
      flag_slt_not_bool @
      flag_ule_not_bool @
      flag_sle_not_bool @
      flag_ugt_not_bool @
      flag_sgt_not_bool @
      flag_uge_not_bool @
      flag_sge_not_bool @
      extend_flag @
      trunc_flag @
      extend_i8 @
      double_extend @
      extend_nop @
      itrunc_nop @
      itrunc_extend_nop @
      br_const @
      sel_const @
      sel_bool @
      prop_copy @
      []
  end

  let rules = Egraph.create_table Groups.all
end

let run tenv fn = Egraph.run fn tenv Rules.rules
