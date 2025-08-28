open Regular.Std

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
    val args : ?rev:bool -> t -> Var.t seq
    val insns : ?rev:bool -> t -> Insn.t seq
    val ctrl : t -> Ctrl.t
  end

  module Func : sig
    type t
    val dict : t -> Dict.t
    val with_tag : t -> 'a Dict.tag -> 'a -> t
    val name : t -> string
    val blks : ?rev:bool -> t -> Blk.t seq
    val update_blks_exn : t -> Blk.t list -> t
  end

  module Cfg : sig
    include Label.Graph_s
    val create : Func.t -> t
  end

  module Live : Live_intf.S
    with type var := Var.t
     and type var_comparator := Var.comparator_witness
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
  live : 'live;                     (* Liveness analysis. *)
  cfg  : 'cfg;                      (* Control-flow graph. *)
  dom  : Label.t Semi_nca.tree;     (* Dominator tree. *)
  df   : Label.t Semi_nca.frontier; (* Dominance frontier. *)
  blks : 'blk Label.Table.t;        (* Current version of each block. *)
}
