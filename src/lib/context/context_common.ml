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

type ctx = {
  state : state;
  local : Dict.t;
}

module M = Sm.Make(struct
    type state = ctx
    let error_prefix = "Context error"
  end)

include M.Syntax

type 'a t = 'a M.m

let target = M.gets @@ fun s -> s.state.target
