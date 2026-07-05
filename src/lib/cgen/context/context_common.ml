open Core
module Regular = Cgen_utils.Regular

type state = {
  target    : Target.t;
  nextvar   : int;
  nextlabel : int;
} [@@deriving bin_io, compare, equal, hash, sexp]

module State = struct
  type t = state
  include Regular.Make(struct
      type t = state [@@deriving bin_io, compare, equal, hash, sexp]
      let pp ppf s = Format.fprintf ppf "%a" Sexp.pp_hum @@ sexp_of_state s
    end)
end

type ctx = {
  state : state;
  local : Dict.t;
}

let error_prefix = "Context error"

module M = Cgen_utils.Monads.Sm.Make(struct
    type state = ctx
    type error = Error.t
    let of_or_error e = Error.tag e ~tag:error_prefix
  end)

include M.Syntax

type 'a t = 'a M.m

let target = M.gets @@ fun s -> s.state.target
let when_ = M.when_
let unless = M.unless
let map_list_err = M.map_list_err
let iter_list_err = M.iter_list_err
let map_seq_err = M.map_seq_err
let iter_seq_err = M.iter_seq_err
