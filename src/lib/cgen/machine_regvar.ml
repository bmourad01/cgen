open Core
open Regular.Std

type cls = GPR | FP [@@deriving bin_io, compare, equal, hash, sexp]

let pp_cls ppf = function
  | GPR -> Format.fprintf ppf "gpr"
  | FP -> Format.fprintf ppf "fp"

let cls_of_ty : [< Type.basic | `flag | `v128] -> cls = function
  | #Type.imm | `flag -> GPR
  | #Type.fp | `v128 -> FP

module type S = sig
  type t
  type reg

  val empty_sentinel : t
  val reg : reg -> t
  val var : Var.t -> t
  val is_reg : t -> bool
  val is_var : t -> bool
  val has_reg : t -> reg -> bool
  val has_var : t -> Var.t -> bool
  val which : t -> (reg, Var.t) Either.t

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
      | Nil
      | Reg of R.t
      | Var of Var.t
    [@@deriving bin_io, compare, equal, hash, sexp]
  end

  include T

  let empty_sentinel = Nil

  let is_reg = function
    | Nil -> false
    | Reg _ -> true
    | Var _ -> false

  let is_var = function
    | Nil -> false
    | Reg _ -> false
    | Var _ -> true

  let has_reg t r = match t with
    | Nil -> false
    | Reg r' -> R.equal r r'
    | Var _ -> false

  let has_var t v = match t with
    | Nil -> false
    | Var v' -> Var.(v = v')
    | Reg _ -> false

  let reg r = Reg r
  let var v = Var v

  let which = function
    | Nil -> failwith "which: empty_sentinel"
    | Reg r -> First r
    | Var v -> Second v

  let pp ppf = function
    | Nil -> Format.fprintf ppf "<nil>"
    | Reg r -> Format.fprintf ppf "%a" R.pp r
    | Var v -> Format.fprintf ppf "%a" Var.pp v

  include Regular.Make(struct
      include T
      let pp = pp
      let version = "0.1"
      let module_name = Some N.module_name
    end)
end
