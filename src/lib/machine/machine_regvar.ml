(* Helper module for making the boilerplate stuff for `Regvar`
   as required by the `Machine_intf.S` signature. *)

open Core
open Regular.Std

module type Reg = sig
  type t [@@deriving bin_io, compare, equal, hash, sexp]
  val pp : Format.formatter -> t -> unit
end

module type Name = sig
  val module_name : string
end

module Make(R : Reg)(N : Name) = struct
  module T = struct
    type t =
      | Reg of R.t
      | Var of Var.t
    [@@deriving bin_io, compare, equal, hash, sexp]
  end

  include T

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

  include Regular.Make(struct
      include T
      let pp = pp
      let version = "0.1"
      let module_name = Some N.module_name
    end)
end
