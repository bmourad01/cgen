(* Callbacks for our rewrite rules. *)

open Core
open Monads.Std

module O = Monad.Option
module Subst = Egraph.Subst

open Egraph.Rule
open O.Let
open O.Syntax

let bv t = Bv.modular @@ Type.sizeof_imm t

(* pre: x is nonzero *)
let ctz f x = f @@ Int64.ctz @@ Bv.to_int64 x

let is_const x env =
  Subst.find env x |>
  Option.bind ~f:Subst.const |>
  Option.is_some

let is_const2 x y env =
  Option.is_some begin
    let* _ = Subst.find env x >>= Subst.const in
    Subst.find env y >>= Subst.const
  end

let is_not_const x env = match Subst.find env x with
  | Some s -> Option.is_none @@ Subst.const s
  | None ->
    (* We don't know if it's const or not, because we don't have
       a substitution for it. It would be unsafe to answer in the
       affirmative in this case. *)
    false

let is_neg_const x env =
  Option.is_some begin
    let* s = Subst.find env x in
    Subst.const s >>= function
    | `int (x, t) ->
      let module B = (val bv t) in
      O.guard @@ B.msb x
    | _ -> None
  end

(* `x` is not 0 or 1 *)
let is_not_bool x env =
  Option.value ~default:false begin
    Subst.find env x >>= Subst.const >>= function
    | `int (i, _) -> !!Bv.(i <> one && i <> zero)
    | _ -> None
  end

(* `x` is (signed) greater than 1 *)
let is_sgt_one x env =
  Option.value ~default:false begin
    Subst.find env x >>= Subst.const >>= function
    | `int (i, ty) ->
      let m = Bv.modulus @@ Type.sizeof_imm ty in
      !!(Bv.signed_compare i Bv.one m > 0)
    | _ -> None
  end

(* `x` is (signed) less than 0 *)
let is_slt_zero x env =
  Option.value ~default:false begin
    Subst.find env x >>= Subst.const >>= function
    | `int (i, ty) ->
      let m = Bv.modulus @@ Type.sizeof_imm ty in
      !!(Bv.signed_compare i Bv.zero m < 0)
    | _ -> None
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
    let module B = (val bv ty) in
    let+ () = O.guard begin
        let open Bv in
        i <> zero &&
        B.(i land pred i) = zero
      end in
    let sh = ctz B.int i in
    Op.(lsl_ ty x (int sh ty))
  | _ -> None

(* For a signed division by a power of two `n` modulo `k` bits, rewrite to:

   (x < 0 ? x + (y-1) : x) >>> n when x > 2

   ((x >> (k-1)) + x) >>> 1 otherwise
*)
let div_imm_pow2 x y env =
  Subst.find env y >>= Subst.const >>= function
  | `int (i, ty) ->
    let module B = (val bv ty) in
    let+ () = O.guard begin
        let open Bv in
        i <> zero &&
        i <> one &&
        B.(i land pred i) = zero
      end in
    let n = ctz B.int i in
    let i1 = B.pred i in
    let s = B.(int (Type.sizeof_imm ty) - one) in
    let tb = (ty :> Type.basic) in
    if Bv.(i > B.int 2) then
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
        i <> B.pred zero &&
        i <> zero &&
        i <> one &&
        B.(i land pred i) <> zero
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
    let module B = (val bv ty) in
    let+ () = O.guard begin
        let open Bv in
        i <> zero &&
        i <> one &&
        B.(i land pred i) = zero
      end in
    let module B = (val bv ty) in
    let tb = (ty :> Type.basic) in
    let ss = B.(int (Type.sizeof_imm ty) - one) in
    let n = ctz B.int i in
    let su = B.(int (Type.sizeof_imm ty) - n) in
    let t = Op.(lsr_ ty (asr_ ty x (int ss ty)) (int su ty)) in
    Op.(sub tb (and_ ty (add tb x t) (int (B.pred i) ty)) t)
  | _ -> None

(* Dynamically rewrite an unsigned division by a power of two into
   a right shift. *)
let udiv_imm_pow2 x y env =
  Subst.find env y >>= Subst.const >>= function
  | `int (i, ty) ->
    let module B = (val bv ty) in
    let+ () = O.guard begin
        let open Bv in
        i <> zero &&
        B.(i land pred i) = zero
      end in
    let sh = ctz B.int i in
    Op.(lsr_ ty x (int sh ty))
  | _ -> None

(* Dynamically rewrite an unsigned remainder by a power of two into
   a bitwise AND. *)
let urem_imm_pow2 x y env =
  Subst.find env y >>= Subst.const >>= function
  | `int (i, ty) ->
    let module B = (val bv ty) in
    let i' = B.pred i in
    let+ () = O.guard begin
        let open Bv in
        i <> zero &&
        B.(i land i') = zero
      end in
    Op.(and_ ty x (int i' ty))
  | _ -> None

(* Turn an unsigned division/remainder by a constant non-power of two
   into a series of multiplications and shifts. *)
let udiv_urem_imm_non_pow2 ?(rem = false) x y env =
  Subst.find env y >>= Subst.const >>= function
  | `int (i, ty) ->
    let module B = (val bv ty) in
    let+ () = O.guard begin
        let open Bv in
        i <> B.pred zero &&
        i <> zero &&
        i <> one &&
        B.(i land pred i) <> zero
      end in
    let u_mul, u_add, u_shr = Magic_div.unsigned i ty in
    let tb = (ty :> Type.basic) in
    let q1 = Op.(umulh ty x (int u_mul ty)) in
    let qf =
      if u_add then
        let sh = B.int (u_shr - 1) in
        Op.(lsr_ ty
              (add tb
                 (lsr_ ty
                    (sub tb x q1)
                    (int B.one ty))
                 q1)
              (int sh ty))
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
    let i' = B.pred i in
    let* () = O.guard begin
        let open Bv in
        i <> B.pred i &&
        i <> zero &&
        i <> one &&
        B.(i land i') <> zero
      end in
    let tb = (ty :> Type.basic) in
    let i1 = B.succ i in
    if Bv.(B.(i1 land i) = zero) then
      if Bv.(i = B.int 3) then
        (* Special case when n is 3, we bias towards the lower
           power of two. Shift-and-add addressing modes are common
           on several architectures. *)
        !!Op.(add tb (lsl_ ty x (int B.one ty)) x)
      else
        (* Next integer is a power of two, so shift up to it
           and then subtract x. *)
        let sh = ctz B.int i1 in
        !!Op.(sub tb (lsl_ ty x (int sh ty)) x)
    else if Bv.(B.(i' land pred i') = zero) then
      (* Previous integer is a power of two, so shift up to
         it and add x. *)
      let sh = ctz B.int i' in
      !!Op.(add tb (lsl_ ty x (int sh ty)) x)
    else
      (* At this point, the MSB must be zero. *)
      let+ () = O.guard @@ not @@ B.msb i in
      (* Check the next and previous power of two, and see which
         one is closer. We'll add or subtract the remaining factor
         from the shift, which can be recursively rewritten. If we
         end up doing this too many times then it will outweigh the
         cost of just using a `mul` instruction. *)
      let n = Bv.to_int64 i in
      let z = B.int64 @@ Int64.floor_pow2 n in
      let z' = B.int64 @@ Int64.ceil_pow2 n in
      let d = B.(i - z) in
      let d' = B.(z' - i) in
      if Bv.(d <= d') then
        let sh = ctz B.int z in
        Op.(add tb
              (lsl_ ty x (int sh ty))
              (mul tb x (int d ty)))
      else
        let sh = ctz B.int z' in
        Op.(sub tb
              (lsl_ ty x (int sh ty))
              (mul tb x (int d' ty)))
  | _ -> None

let identity_same_type x ty env =
  let* tx = Subst.find env x >>= Subst.typeof in
  let+ () = O.guard @@ Type.equal tx ty in
  var x

let is_rotate_const x y env =
  Option.is_some begin
    let* xi = Subst.find env x >>= Subst.const in
    let* yi = Subst.find env y >>= Subst.const in
    match xi, yi with
    | `int (xi, xt), `int (yi, yt) when Type.equal_imm xt yt ->
      let module B = (val bv xt) in
      let sz = B.int @@ Type.sizeof_imm xt in
      (* Ignore if one of the shift values is greater than or
         equal to the width of the type. *)
      let* () = O.guard Bv.(xi < sz && yi < sz) in
      Option.some_if Bv.(xi = B.(sz - yi)) ()
    | _ -> None
  end
