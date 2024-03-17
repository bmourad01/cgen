open Regular.Std

module type S = sig
  type t
  type func

  (** [find t x] finds the set of uses for the variable [x].

      If a label resolves to a block, then the use site is the
      control-flow instruction of the corresponding block.
  *)
  val find : t -> Var.t -> Label.t seq

  (** Computes the usage sites for a function.

      The function is assumed to be in SSA form.
  *)
  val compute : func -> t
end
