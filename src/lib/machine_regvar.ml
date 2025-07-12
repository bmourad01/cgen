open Core
open Regular.Std

type cls = GPR | FP [@@deriving bin_io, compare, equal, hash, sexp]

let pp_cls ppf = function
  | GPR -> Format.fprintf ppf "gpr"
  | FP -> Format.fprintf ppf "fp"

module type S = sig
  type t
  type reg

  val reg : reg -> t
  val var : cls -> Var.t -> t
  val is_reg : t -> bool
  val is_var : t -> bool
  val has_reg : t -> reg -> bool
  val has_var : t -> Var.t -> bool
  val which : t -> (reg, Var.t * cls) Either.t

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
      | Var of Var.t * cls
    [@@deriving bin_io, compare, equal, hash, sexp]
  end

  include T

  let is_reg = function
    | Reg _ -> true
    | Var _ -> false

  let is_var = function
    | Reg _ -> false
    | Var _ -> true

  let has_reg t r = match t with
    | Reg r' -> R.equal r r'
    | Var _ -> false

  let has_var t v = match t with
    | Var (v', _) -> Var.(v = v')
    | Reg _ -> false
  
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
