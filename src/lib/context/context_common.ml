open Core
open Regular.Std

type state = {
  target    : Target.t;
  nextvar   : Int63.t;
  nextlabel : Int63.t;
} [@@deriving bin_io, compare, equal, hash, sexp]

module State = struct
  type t = state
  include Regular.Make(struct
      type t = state [@@deriving bin_io, compare, equal, hash, sexp]
      let pp ppf s = Format.fprintf ppf "%a" Sexp.pp_hum @@ sexp_of_state s
      let version = "0.1"
      let module_name = Some "Cgen.Context.State"
    end)
end

type ctx = {
  state : state;
  local : Dict.t;
}

let error_prefix = "Context error"

module M = Sm.Make(struct
    type state = ctx
    let error_prefix = error_prefix
  end)

include M.Syntax

type 'a t = 'a M.m

let target = M.gets @@ fun s -> s.state.target
let when_ = M.when_
let unless = M.unless
