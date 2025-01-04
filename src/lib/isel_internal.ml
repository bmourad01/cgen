open Core
open Virtual.Abi

module Pattern = struct
  type op =
    | Oaddr     of Bv.t
    | Obinop    of Insn.binop
    | Obool     of bool
    | Obr
    | Odouble   of float
    | Ojmp
    | Oint      of Bv.t * Type.imm
    | Oload     of Var.t * Type.arg
    | Olocal    of Label.t
    | Oret
    | Osel      of Type.basic
    | Osingle   of Float32.t
    | Ostore    of Type.arg * Label.t
    | Osym      of string * int
    | Ounop     of Insn.unop
  [@@deriving compare, equal, hash, sexp]

  type t =
    | V of string
    | C of string * [Type.basic | `sym]
    | P of op * t list
  [@@deriving compare, equal, hash, sexp]
end

module Subst = struct
  type 'r term =
    | Regvar of 'r * Type.basic
    | Imm of Bv.t * Type.imm
    | Single of Float32.t
    | Double of float
    | Sym of string * int
    | Label of Label.t

  type 'r t = 'r term String.Map.t

  let find = Map.find
end

module Rule = struct
  type ('r, 'i) callback = 'r Subst.t -> 'i list option
  type ('r, 'i) t = Pattern.t * ('r, 'i) callback
  let (=>) pre post = pre, post
end
