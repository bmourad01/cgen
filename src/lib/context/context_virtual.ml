open Core

module Var = Context_var
module Label = Context_label
module M = Context_common.M

open M.Syntax

let insn ?(dict = Dict.empty) op =
  let+ label = Label.fresh in
  Virtual.Insn.create op ~label ~dict

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

let call0 ?(dict = Dict.empty) f args vargs =
  insn (`call (None, f, args, vargs)) ~dict

let call ?(dict = Dict.empty) t f args vargs =
  let* var = Var.fresh in
  let+ i = insn (`call (Some (var, t), f, args, vargs)) ~dict in
  var, i

let load ?(dict = Dict.empty) t a =
  let* var = Var.fresh in
  let+ i = insn (`load (var, t, a)) ~dict in
  var, i

let store ?(dict = Dict.empty) t v a =
  insn (`store (t, v, a)) ~dict

let vaarg ?(dict = Dict.empty) t a =
  let* var = Var.fresh in
  let+ i = insn (`vaarg (var, t, a)) ~dict in
  var, i

let vastart ?(dict = Dict.empty) a =
  insn (`vastart a) ~dict

let blits32 = [
  `i32, 4;
  `i16, 2;
  `i8,  1;
]

let blits64 = (`i64, 8) :: blits32

module type Blit_intf = sig
  type insn
  val add : Type.basic -> Virtual.operand -> Virtual.operand -> (Var.t * insn) M.m
  val load : Type.imm -> Virtual.operand -> (Var.t * insn) M.m
  val store : Type.imm -> Virtual.operand -> Virtual.operand -> insn M.m
end

module Make_blit(L : Blit_intf) = struct
  let go ?(ignore_dst = false) word src dst size =
    let fwd = size >= 0 in
    let wi = (word :> Type.imm) in
    let wb = (word :> Type.basic) in
    let wordsz = Type.sizeof_imm_base word in
    let md = Bv.modulus wordsz in
    let rec consume ty is sz off = function
      | n when sz < n -> !!(is, sz, off)
      | n ->
        let off = off - (if fwd then 0 else n) in
        let o = `int (Bv.(int off mod md), wi) in
        (* Copy from src. *)
        let* a1, ai1 =
          if off = 0 then
            !!(`var src, [])
          else
            let+ a1, ai1 = L.add wb (`var src) o in
            `var a1, [ai1] in
        let* l, ld = L.load ty a1 in
        (* Store to dst. *)
        let* sts = if not ignore_dst then
            let* a2, ai2 =
              if off = 0 then
                !!(`var dst, [])
              else
                let+ a2, ai2 = L.add wb (`var dst) o in
                `var a2, [ai2] in
            let+ st = L.store ty (`var l) a2 in
            st :: ai2
          else !![] in
        (* Accumulate insns in reverse order. *)
        let is = sts @ (ld :: ai1) @ is in
        let off = off + (if fwd then n else 0) in
        consume ty is (sz - n) off n in
    let+ blit, _, _ =
      let sz = Int.abs size in
      let off = if fwd then 0 else sz in
      let blits = match word with
        | `i32 -> blits32
        | `i64 -> blits64 in
      M.List.fold blits ~init:([], sz, off)
        ~f:(fun ((is, sz, off) as acc) (ty, by) ->
            if sz <= 0 then !!acc
            else consume ty is sz off by) in
    List.rev blit
  [@@specialise]
end

module Blit = Make_blit(struct
    type insn = Virtual.insn
    let add ty x y = binop (`add ty) x y
    let load ty a = load (ty :> Type.arg) a
    let store ty v a = store (ty :> Type.arg) v a
  end)

let blit ~src ~dst word size = Blit.go word src dst size
let ldm word src size = Blit.go word src src size ~ignore_dst:true

let blk ?(dict = Dict.empty) ?(args = []) ?(insns = []) ~ctrl () =
  let+ label = Label.fresh in
  Virtual.Blk.create ~dict ~args ~insns ~ctrl ~label ()

let blk'
    ?(dict = Dict.empty)
    ?(label = None)
    ?(args = [])
    ?(insns = [])
    ~ctrl () =
  let* insns = M.List.map insns ~f:insn in
  let+ label = match label with
    | None -> Label.fresh
    | Some l -> !!l in
  Virtual.Blk.create ~dict ~args ~insns ~ctrl ~label ()
