open Core

module type S = sig
  type lhs
  type insn
  type blk
  type func

  type resolved = [
    | `blk  of blk
    | `insn of insn * blk * lhs * int
  ]

  type def = [
    | resolved
    | `slot
    | `arg
    | `blkarg of blk
  ]

  type t

  (** Attempt to resolve the label to some definition in the
      function.

      [`blk b]: the label resolved to block [b].

      [`insn (i, b, lhs, ord)]: the label resolved to instruction [i],
      in block [b], defining [lhs]. [ord] is the relative ordering of
      [i] in block [b] such that, given an [i'] and [ord'] also in [b],
      [ord < ord'] implies that [i] appears before [i'].
  *)
  val resolve : t -> Label.t -> resolved option

  (** Attempt to resolve the variable to its definition.

      [`blk b]: the variable was defined as a parameter of block [b].

      [`insn (i, b, lhs, ord)]: the variable was defined at instruction
      [i] in block [b], and is a member of [lhs].

      [`slot]: the variable is a slot.

      [`arg]: the variable is an argument of the function.

      [`blkarg b]: the variable is an argument of block [b].
  *)
  val def : t -> Var.t -> def option

  (** Attempt to resolve the variable to its usage sites.

      [`blk b]: the variable was used at the control-flow instruction
      of block [b].

      [`insn (i, b, _, _)]: the variable was used at instruction [i] in
      block [b].
  *)
  val uses : t -> Var.t -> resolved list

  (** Compute the resolution data for a function.

      Returns [Error _] if there are duplicate definitions.
  *)
  val create : func -> t Or_error.t
end
