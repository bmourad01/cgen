open Core
open Graphlib.Std

module type S = sig
  type t
  type var
  type var_comparator
  type blk
  type func
  type cfg

  (** [compute fn ~keep] solves the data flow equations for liveness in
      the function [fn].

      [keep] is a set of variables that are initially live on the exit
      nodes of the function.
  *)
  val compute : ?keep:(var, var_comparator) Set.t -> func -> t

  (** Same as [compute], but for an already computed CFG and block mapping. *)
  val compute' : ?keep:(var, var_comparator) Set.t -> cfg -> blk Label.Tree.t -> t

  (** The set of live-in variables at the block assicated with the label. *)
  val ins : t -> Label.t -> (var, var_comparator) Set.t

  (** The set of live-out variables at the block assicated with the label. *)
  val outs : t -> Label.t -> (var, var_comparator) Set.t

  (** The set of blocks where the variable is live-in. *)
  val blks : t -> var -> Label.Set.t

  (** The set of variables that were defined in the block associated with
      the label. *)
  val defs : t -> Label.t -> (var, var_comparator) Set.t

  (** The set of variables that were used in the block associated with the
      label.

      Note that this set only includes the free variables of the block.
  *)
  val uses : t -> Label.t -> (var, var_comparator) Set.t

  (** Folds over the live-ins of each block.

      Applies [f] to the live-in set of each block in the function.
  *)
  val fold : t -> init:'a -> f:('a -> Label.t -> (var, var_comparator) Set.t -> 'a) -> 'a

  (** Returns the solution of the data-flow equations, which is a mapping
      from block labels to their live-out sets. *)
  val solution : t -> (Label.t, (var, var_comparator) Set.t) Solution.t

  (** Pretty-prints the live-in sets for each block. *)
  val pp : Format.formatter -> t -> unit
end

