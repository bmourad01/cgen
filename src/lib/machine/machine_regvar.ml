(* Helper module for making the boilerplate stuff for `Regvar`
   as required by the `Machine_intf.S` signature. *)

open Core

module type Reg = sig
  type t [@@deriving bin_io, compare, equal, sexp]
  val pp : Format.formatter -> t -> unit
end

module Make(R : Reg) = struct
  module T = struct
    type t =
      | Reg of R.t
      | Var of Var.t
    [@@deriving bin_io, compare, equal, sexp]
  end

  module C = struct
    include T
    include Comparator.Make(T)
  end
  include C
  module Set = Set.Make(C)

  let is_reg = function
    | Reg _ -> true
    | Var _ -> false

  let is_var = function
    | Reg _ -> false
    | Var _ -> true

  let reg r = Reg r
  let var v = Var v

  let which = function
    | Reg r -> First r
    | Var v -> Second v

  let pp ppf = function
    | Reg r -> Format.fprintf ppf "%a" R.pp r
    | Var v -> Format.fprintf ppf "%a" Var.pp v
end
