open Core
open Virtual.Abi

module Pattern = struct
  type op =
    | Oaddr   of Bv.t
    | Obinop  of Insn.binop
    | Obool   of bool
    | Obr
    | Ocall
    | Odouble of float
    | Ohlt
    | Ojmp
    | Oint    of Bv.t * Type.imm
    | Oload   of Type.basic
    | Olocal  of Label.t
    | Omove
    | Oret
    | Osel    of Type.basic
    | Osingle of Float32.t
    | Ostore  of [Type.basic | `v128]
    | Osym    of string * int
    | Ounop   of Insn.unop
  [@@deriving compare, equal, hash, sexp]

  type t =
    | V of string
    | P of op * t list
  [@@deriving compare, equal, hash, sexp]

  let pp_op ppf = function
    | Oaddr a -> Format.fprintf ppf "addr:%a" Bv.pp a
    | Obinop b -> Format.fprintf ppf "%a" Insn.pp_binop b
    | Obool b -> Format.fprintf ppf "%b" b
    | Obr -> Format.fprintf ppf "br"
    | Ocall -> Format.fprintf ppf "call"
    | Odouble d -> Format.fprintf ppf "%a_d" Float.pp d
    | Ohlt -> Format.fprintf ppf "hlt"
    | Ojmp -> Format.fprintf ppf "jmp"
    | Oint (i, t) -> Format.fprintf ppf "%a_%a" Bv.pp i Type.pp_imm t
    | Oload t -> Format.fprintf ppf "ld.%a" Type.pp_basic t
    | Olocal l -> Format.fprintf ppf "%a" Label.pp l
    | Omove -> Format.fprintf ppf "move"
    | Oret -> Format.fprintf ppf "ret"
    | Osel t -> Format.fprintf ppf "sel.%a" Type.pp_basic t
    | Osingle s -> Format.fprintf ppf "%s_s" (Float32.to_string s)
    | Ostore `v128 -> Format.fprintf ppf "st.v"
    | Ostore (#Type.basic as t) -> Format.fprintf ppf "st.%a" Type.pp_basic t
    | Osym (s, o) -> Format.fprintf ppf "$%s+%d" s o
    | Ounop u -> Format.fprintf ppf "%a" Insn.pp_unop u
end

module Subst = struct
  type 'r term =
    | Regvar of 'r * Type.basic
    | Imm of Bv.t * Type.imm
    | Single of Float32.t
    | Double of float
    | Sym of string * int
    | Label of Label.t
    | Bool of bool
  [@@deriving equal]

  type 'r t = 'r term String.Map.t

  let find = Map.find
  let empty = String.Map.empty
end

module Rule(C : Context_intf.S) = struct
  type ('r, 'i) callback = 'r Subst.t -> 'i list option C.t
  type ('r, 'i) t = Pattern.t * ('r, 'i) callback
  let (=>) pre post = pre, post
end
