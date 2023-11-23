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
