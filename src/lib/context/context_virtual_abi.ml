open Core

module Var = Context_var
module Label = Context_label
module M = Context_common.M

open M.Syntax

let insn ?(dict = Dict.empty) op =
  let+ label = Label.fresh in
  Virtual.Abi.Insn.create op ~label ~dict

let binop ?(dict = Dict.empty) b l r =
  let* var = Var.fresh in
  let+ i = insn (`bop (var, b, l, r)) ~dict in
  var, i

let unop ?(dict = Dict.empty) u a =
  let* var = Var.fresh in
  let+ i = insn (`uop (var, u, a)) ~dict in
  var, i

let sel ?(dict = Dict.empty) t c y n =
  let* var = Var.fresh in
  let+ i = insn (`sel (var, t, c, y, n)) ~dict in
  var, i

let call ?(dict = Dict.empty) rs f args =
  let* xs = M.List.map rs ~f:(fun (t, r) ->
      let+ x = Var.fresh in
      x, t, r) in
  let+ i = insn (`call (xs, f, args)) ~dict in
  xs, i

let load ?(dict = Dict.empty) t a =
  let* var = Var.fresh in
  let+ i = insn (`load (var, t, a)) ~dict in
  var, i

let store ?(dict = Dict.empty) t v a =
  insn (`store (t, v, a)) ~dict

let loadreg ?(dict = Dict.empty) t r =
  let* var = Var.fresh in
  let+ i = insn (`loadreg (var, t, r)) ~dict in
  var, i

let storereg ?(dict = Dict.empty) r a =
  insn (`storereg (r, a)) ~dict

let setreg ?(dict = Dict.empty) r a =
  insn (`setreg (r, a)) ~dict

let stkargs ?(dict = Dict.empty) () =
  let* var = Var.fresh in
  let+ i = insn (`stkargs var) ~dict in
  var, i

let blit_aux ?(ignore_dst = false) word src dst size =
  let fwd = size >= 0 in
  let wi = (word :> Type.imm) in
  let wb = (word :> Type.basic) in
  let wordsz = Type.sizeof_imm_base word in
  let md = Bv.modulus wordsz in
  let rec consume ty is sz off n =
    if sz >= n then
      let off = off - (if fwd then 0 else n) in
      let o = `int (Bv.(int off mod md), wi) in
      (* Copy from src. *)
      let* a1, ai1 =
        if off = 0 then
          !!(src, [])
        else
          let+ a1, ai1 = binop (`add wb) (`var src) o in
          a1, [ai1] in
      let* l, ld = load ty (`var a1) in
      (* Store to dst. *)
      let* sts = if not ignore_dst then
          let* a2, ai2 =
            if off = 0 then
              !!(dst, [])
            else
              let+ a2, ai2 = binop (`add wb) (`var dst) o in
              a2, [ai2] in
          let+ st = store ty (`var l) (`var a2) in
          st :: ai2
        else !![] in
      (* Accumulate insns in reverse order. *)
      let is = sts @ (ld :: ai1) @ is in
      let off = off + (if fwd then n else 0) in
      consume ty is (sz - n) off n
    else !!(is, sz, off) in
  let+ blit, _, _ =
    let sz = Int.abs size in
    let off = if fwd then 0 else sz in
    let blits = match word with
      | `i32 -> Context_virtual.blits32
      | `i64 -> Context_virtual.blits64 in
    M.List.fold blits ~init:([], sz, off)
      ~f:(fun ((is, sz, off) as acc) (ty, by) ->
          if sz <= 0 then !!acc
          else consume ty is sz off by) in
  List.rev blit
[@@specialise]

let blit ~src ~dst word size = blit_aux word src dst size
let ldm word src size = blit_aux word src src size ~ignore_dst:true
