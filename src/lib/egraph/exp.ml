open Core
open Virtual

type 'a pure =
  | Palloc  of 'a * int
  | Pbinop  of 'a * Insn.binop * 'a pure * 'a pure
  | Pbool   of bool
  | Pcall   of 'a * Type.basic * 'a global * 'a pure list * 'a pure list
  | Pdouble of float
  | Pint    of Bv.t * Type.imm
  | Pload   of 'a * Type.basic * 'a pure
  | Psel    of 'a * Type.basic * 'a pure * 'a pure * 'a pure
  | Psingle of Float32.t
  | Psym    of string * int
  | Punop   of 'a * Insn.unop * 'a pure
  | Pvar    of Var.t
[@@deriving bin_io, compare, equal, sexp]

and 'a global =
  | Gaddr of Bv.t
  | Gpure of 'a pure
  | Gsym  of string
[@@deriving bin_io, compare, equal, sexp]

and 'a local = Label.t * 'a pure list
[@@deriving bin_io, compare, equal, sexp]

and 'a dst =
  | Dglobal of 'a global
  | Dlocal  of 'a local
[@@deriving bin_io, compare, equal, sexp]

type 'a table = (Bv.t * 'a local) list
[@@deriving bin_io, compare, equal, sexp]

type 'a t =
  | Ebr      of 'a pure * 'a dst * 'a dst
  | Ecall    of 'a global * 'a pure list * 'a pure list
  | Ejmp     of 'a dst
  | Eret     of 'a pure
  | Eset     of Var.t * 'a pure
  | Estore   of Type.basic * 'a pure * 'a pure
  | Esw      of Type.imm * 'a pure * 'a local * 'a table
[@@deriving bin_io, compare, equal, sexp]
