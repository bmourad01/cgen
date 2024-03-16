open Core
open Graphlib.Std

type tran = {
  defs  : Var.Set.t;
  uses  : Var.Set.t;
  insns : Var.Set.t Label.Tree.t;
}

let empty_tran = {
  defs  = Var.Set.empty;
  uses  = Var.Set.empty;
  insns = Label.Tree.empty;
}

let pp_vars ppf vars =
  Format.pp_print_list
    ~pp_sep:Format.pp_print_space
    Var.pp ppf (Set.to_list vars)

let pp_transfer ppf {uses; defs; _} =
  Format.fprintf ppf "(%a) / (%a)" pp_vars uses pp_vars defs

let (++) = Set.union and (--) = Set.diff
let apply {defs; uses; _} vars = vars -- defs ++ uses

module type S = sig
  type t
  type func

  (** [compute fn ~keep] solves the data flow equations for liveness in
      the function [fn].

      [keep] is a set of variables that are initially live on the exit
      nodes of the function.
  *)
  val compute : ?keep:Var.Set.t -> func -> t

  (** The set of live-in variables at the block assicated with the label. *)
  val ins : t -> Label.t -> Var.Set.t

  (** The set of live-out variables at the block assicated with the label. *)
  val outs : t -> Label.t -> Var.Set.t

  (** The set of blocks where the variable is live-in. *)
  val blks : t -> Var.t -> Label.Set.t

  (** The set of variables that were defined in the block associated with
      the label. *)
  val defs : t -> Label.t -> Var.Set.t

  (** Returns the live-out mappings for each instruction in a given block.

      Note that this mapping does not cross block boundaries. It should be
      used to identify variables that are live within the scope of a single
      block.
  *)
  val insns : t -> Label.t -> Var.Set.t Label.Tree.t

  (** The set of variables that were used in the block associated with the
      label.

      Note that this set only includes the free variables of the block.
  *)
  val uses : t -> Label.t -> Var.Set.t

  (** Folds over the live-ins of each block.

      Applies [f] to the live-in set of each block in the function.
  *)
  val fold : t -> init:'a -> f:('a -> Label.t -> Var.Set.t -> 'a) -> 'a

  (** Returns the solution of the data-flow equations, which is a mapping
      from block labels to their live-out sets. *)
  val solution : t -> (Label.t, Var.Set.t) Solution.t

  (** Pretty-prints the live-in sets for each block. *)
  val pp : Format.formatter -> t -> unit
end

