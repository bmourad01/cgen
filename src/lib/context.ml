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
  let insn ?(dict = Dict.empty) d =
    let+ label = Label.fresh in
    Virtual.Insn.create d ~label ~dict

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
