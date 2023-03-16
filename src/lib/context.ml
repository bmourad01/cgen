open Core
open Monads.Std
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
    let fail msg = Error.createf "Context error: %s" msg
  end)

include M
include M.Syntax

type 'a t = 'a m

let target = gets @@ fun s -> s.target

type var = Var.t

module Var = struct
  let fresh =
    let* s = get () in
    let id = s.nextvar in
    let+ () = put {s with nextvar = Int63.succ id} in
    Var.temp (Obj.magic id : Var.id)
end

type label = Label.t

module Label = struct
  let init = Int63.(succ (Obj.magic Label.pseudoexit : t))

  let fresh =
    let* s = get () in
    let l = s.nextlabel in
    let+ () = put {s with nextlabel = Int63.succ l} in
    (Obj.magic l : Label.t)
end

module Virtual = struct
  module Insn = struct
    let data d =
      let+ label = Label.fresh in
      Virtual.Insn.data d ~label
  end

  let blk ?(args = []) ?(data = []) ~ctrl () =
    let+ label = Label.fresh in
    Virtual.Blk.create ~args ~data ~ctrl ~label ()

  let blk' ?(label = None) ?(args = []) ?data:(d = []) ~ctrl () =
    let* data = List.map d ~f:Insn.data in
    let+ label = match label with
      | None -> Label.fresh
      | Some l -> !!l in
    Virtual.Blk.create ~args ~data ~ctrl ~label ()
end

let init target = {
  target;
  nextvar = Int63.zero;
  nextlabel = Label.init;
}

let reject err = Error err
let run x s = x.run s ~reject ~accept:(fun x s -> Ok (x, s))
let eval x s = x.run s ~reject ~accept:(fun x _ -> Ok x)
