(* Helper module for making the boilerplate stuff for `Regvar`
   as required by the `Context.Machine` signature. *)

open Core

module type Reg = sig
  type t [@@deriving compare, equal, sexp]
end

module Make(R : Reg) = struct
  module T = struct
    type t =
      | Reg of R.t
      | Var of Var.t
    [@@deriving compare, equal, sexp] 
  end

  include T
  include Comparator.Make(T)

  let is_reg = function
    | Reg _ -> true
    | Var _ -> false

  let is_var = function
    | Reg _ -> false
    | Var _ -> true

  let reg = function
    | Reg r -> Some r
    | Var _ -> None

  let var = function
    | Reg _ -> None
    | Var v -> Some v

  let which = function
    | Reg r -> First r
    | Var v -> Second v
end
