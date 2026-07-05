
module VT = Var.Dense_table
module LT = Label.Dense_table

exception Missing_blk of Label.t

module type L = sig
  type lhs

  module Insn : sig
    type t
    type op
    val op : t -> op
    val label : t -> Label.t
    val has_label : t -> Label.t -> bool
    val with_op : t -> op -> t
    val lhs : t -> Var.t list
  end

  module Ctrl : sig
    type t
  end

  module Blk : sig
    type t

    val create :
      ?dict:Dict.t ->
      ?args:Var.t list ->
      ?insns:Insn.t list ->
      label:Label.t ->
      ctrl:Ctrl.t ->
      unit ->
      t

    val label : t -> Label.t
    val dict : t -> Dict.t
    val args : ?rev:bool -> t -> Var.t Base.Sequence.t
    val insns : ?rev:bool -> t -> Insn.t Base.Sequence.t
    val ctrl : t -> Ctrl.t
    val fold_insns : ?rev:bool -> t -> init:'a -> f:('a -> Insn.t -> 'a) -> 'a
    val iter_insns : ?rev:bool -> t -> f:(Insn.t -> unit) -> unit
    val fold_args : ?rev:bool -> t -> init:'a -> f:('a -> Var.t -> 'a) -> 'a
    val iter_args : ?rev:bool -> t -> f:(Var.t -> unit) -> unit
    val args_to_list : t -> Var.t list
  end

  module Func : sig
    type t
    val dict : t -> Dict.t
    val with_tag : t -> 'a Dict.tag -> 'a -> t
    val name : t -> string
    val blks : ?rev:bool -> t -> Blk.t Base.Sequence.t
    val iter_reachable : t -> f:(Blk.t -> unit) -> unit
    val num_blks : t -> int
    val num_insns : t -> int
    val update_blks_exn : t -> Blk.t list -> t
  end

  module Cfg : sig
    type t = Label.Graph.t
    val create : Func.t -> t
  end

  module Live : Live_intf.S
    with type var := Var.t
     and type var_set := Var.Tree_set.t
     and type func := Func.t
     and type blk := Blk.t
     and type cfg := Cfg.t

  module Resolver : Resolver_intf.S
    with type lhs := lhs
     and type insn := Insn.t
     and type blk := Blk.t
     and type func := Func.t

  val argify_ctrl : inc:(Label.t -> Var.t list) -> Ctrl.t -> Ctrl.t

  val rename_op :
    stk:(Var.t -> Var.t) ->
    rename:(Var.t -> Var.t) ->
    Insn.op ->
    Insn.op

  val rename_ctrl : stk:(Var.t -> Var.t) -> Ctrl.t -> Ctrl.t
end

type ('live, 'cfg, 'blk) env = {
  live  : 'live;             (* Liveness analysis. *)
  cfg   : 'cfg;              (* Control-flow graph. *)
  dom   : Semi_nca.tree;     (* Dominator tree. *)
  df    : Semi_nca.frontier; (* Dominance frontier. *)
  blks  : 'blk LT.t;         (* Current version of each block. *)
  nvars : int;
}
