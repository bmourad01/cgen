open Core
open Regular.Std

type state = {
  target    : Target.t;
  nextvar   : Int63.t;
  nextlabel : Int63.t;
} [@@deriving bin_io, compare, equal, hash, sexp]

module State = struct
  module T = struct
    type t = state [@@deriving bin_io, compare, equal, hash, sexp]
  end

  include T

  let pp ppf s = Format.fprintf ppf "%a" Sexp.pp_hum @@ sexp_of_state s

  include Regular.Make(struct
      include T
      let pp = pp
      let version = "0.1"
      let module_name = Some "Cgen.Context.State"
    end)
end

module M = Sm.Make(struct
    type nonrec state = state
    let error_prefix = "Context error"
  end)

include M.Syntax

type 'a t = 'a M.m

let target = M.gets @@ fun s -> s.target

type var = Var.t

module Var = struct
  let fresh =
    let* s = M.get () in
    let id = s.nextvar in
    let+ () = M.put {s with nextvar = Int63.succ id} in
    let x = Var_internal.temp id in
    (* XXX: this is ugly, but works *)
    (Obj.magic x : var)
end

type label = Label.t

module Label = struct
  let init = Int63.(succ (Obj.magic Label.pseudoexit : t))

  let fresh =
    let* s = M.get () in
    let l = s.nextlabel in
    let+ () = M.put {s with nextlabel = Int63.succ l} in
    (Obj.magic l : Label.t)
end

module Virtual = struct
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

  let ref ?(dict = Dict.empty) a =
    let* var = Var.fresh in
    let+ i = insn (`ref (var, a)) ~dict in
    var, i

  let unref ?(dict = Dict.empty) s a =
    let* var = Var.fresh in
    let+ i = insn (`unref (var, s, a)) ~dict in
    var, i

  let blits32 = [
    `i32, 4;
    `i16, 2;
    `i8,  1;
  ]

  let blits64 = (`i64, 8) :: blits32

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
            !!(`var src, [])
          else
            let+ a1, ai1 = binop (`add wb) (`var src) o in
            `var a1, [ai1] in
        let* l, ld = load ty a1 in
        (* Store to dst. *)
        let* sts = if not ignore_dst then
            let* a2, ai2 =
              if off = 0 then
                !!(`var dst, [])
              else
                let+ a2, ai2 = binop (`add wb) (`var dst) o in
                `var a2, [ai2] in
            let+ st = store ty (`var l) a2 in
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
        | `i32 -> blits32
        | `i64 -> blits64 in
      M.List.fold blits ~init:([], sz, off)
        ~f:(fun ((is, sz, off) as acc) (ty, by) ->
            if sz <= 0 then !!acc
            else consume ty is sz off by) in
    List.rev blit
  [@@specialise]

  let blit ~src ~dst word size = blit_aux word src dst size
  let ldm word src size = blit_aux word src src size ~ignore_dst:true

  let blk ?(dict = Dict.empty) ?(args = []) ?(insns = []) ~ctrl () =
    let+ label = Label.fresh in
    Virtual.Blk.create ~dict ~args ~insns ~ctrl ~label ()

  let blk'
      ?(dict = Dict.empty)
      ?(label = None)
      ?(args = [])
      ?insns:(d = [])
      ~ctrl () =
    let* insns = M.List.map d ~f:insn in
    let+ label = match label with
      | None -> Label.fresh
      | Some l -> !!l in
    Virtual.Blk.create ~dict ~args ~insns ~ctrl ~label ()

  module Module = struct
    let map_funs m ~f =
      Virtual.Module.funs m |> M.Seq.map ~f >>| fun funs ->
      Seq.to_list funs |> Virtual.Module.with_funs m
  end

  module Abi = struct
    let insn ?(dict = Dict.empty) op =
      let+ label = Label.fresh in
      Virtual.Abi.Insn.create op ~label ~dict

    let binop ?(dict = Dict.empty) b l r =
      let* var = Var.fresh in
      let+ i = insn (`bop (`var var, b, l, r)) ~dict in
      var, i

    let unop ?(dict = Dict.empty) u a =
      let* var = Var.fresh in
      let+ i = insn (`uop (`var var, u, a)) ~dict in
      var, i

    let sel ?(dict = Dict.empty) t c y n =
      let* var = Var.fresh in
      let+ i = insn (`sel (`var var, t, c, y, n)) ~dict in
      var, i

    let call ?(dict = Dict.empty) rs f args =
      insn (`call (rs, f, args)) ~dict

    let load ?(dict = Dict.empty) t a =
      let* var = Var.fresh in
      let+ i = insn (`load (`var var, t, a)) ~dict in
      var, i

    let store ?(dict = Dict.empty) t v a =
      insn (`store (t, v, a)) ~dict

    let storev ?(dict = Dict.empty) v a =
      insn (`storev (v, a)) ~dict

    let blits32 = [
      `i32, 4;
      `i16, 2;
      `i8,  1;
    ]

    let blits64 = (`i64, 8) :: blits32

    let oper (v : Virtual.Abi.var) = (v :> Virtual.Abi.operand)

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
              let+ a1, ai1 = binop (`add wb) (oper src) o in
              `var a1, [ai1] in
          let* l, ld = load ty (oper a1) in
          (* Store to dst. *)
          let* sts = if not ignore_dst then
              let* a2, ai2 =
                if off = 0 then
                  !!(dst, [])
                else
                  let+ a2, ai2 = binop (`add wb) (oper dst) o in
                  `var a2, [ai2] in
              let+ st = store ty (`var l) (oper a2) in
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
          | `i32 -> blits32
          | `i64 -> blits64 in
        M.List.fold blits ~init:([], sz, off)
          ~f:(fun ((is, sz, off) as acc) (ty, by) ->
              if sz <= 0 then !!acc
              else consume ty is sz off by) in
      List.rev blit
    [@@specialise]

    let blit ~src ~dst word size = blit_aux word src dst size
    let ldm word src size = blit_aux word src src size ~ignore_dst:true
  end
end

let init target = {
  target;
  nextvar = Int63.zero;
  nextlabel = Label.init;
}

include M

let reject err = Error err
let run x s = x.run s ~reject ~accept:(fun x s -> Ok (x, s))
let eval x s = x.run s ~reject ~accept:(fun x _ -> Ok x)
