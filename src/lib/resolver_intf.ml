open Core

module type S = sig
  type lhs
  type insn
  type blk
  type func

  (** A resolution of a label.

      [`blk b]: the label resolved to the block [b].

      [`insn (i, b, lhs)]: the label resolved to the instruction
      [i] in block [b], defining [lhs].
  *)
  type resolved = [
    | `blk  of blk
    | `insn of insn * blk * lhs
  ]

  type t

  (** Attempt to resolve the label to some definition in the
      function. *)
  val resolve : t -> Label.t -> resolved option

  (** Attempt to resolve the variable to the block where it was
      defined as an argument thereof. *)
  val blk_arg : t -> Var.t -> Label.t option

  val create : func -> t Or_error.t
end
