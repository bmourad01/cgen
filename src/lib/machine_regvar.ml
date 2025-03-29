open Core
open Regular.Std

module type S = sig
  type t
  type reg

  val reg : reg -> t
  val var : [`gpr | `fp] -> Var.t -> t
  val is_reg : t -> bool
  val is_var : t -> bool
  val which : t -> (reg, Var.t * [`gpr | `fp]) Either.t

  include Regular.S with type t := t
end

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
      | Var of Var.t * [`gpr | `fp]
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
  let var cls v = Var (v, cls)

  let which = function
    | Reg r -> First r
    | Var (v, cls) -> Second (v, cls)

  let pp ppf = function
    | Reg r -> Format.fprintf ppf "%a" R.pp r
    | Var (v, _) -> Format.fprintf ppf "%a" Var.pp v

  include Regular.Make(struct
      include T
      let pp = pp
      let version = "0.1"
      let module_name = Some N.module_name
    end)
end
