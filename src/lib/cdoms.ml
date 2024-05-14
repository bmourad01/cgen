(* Construct the instruction-level dominance relation. *)

open Core
open Regular.Std

type t = parent:Label.t -> Label.t -> bool

module type L = sig
  type lhs

  module Insn : sig
    type t
    val label : t -> Label.t
    val has_label : t -> Label.t -> bool
  end

  module Blk : sig
    type t
    val label : t -> Label.t
    val insns : ?rev:bool -> t -> Insn.t seq
  end

  val is_descendant_of : t
  val resolve : Label.t -> [`blk of Blk.t | `insn of Insn.t * Blk.t * lhs * int] option
end

module Make(M : L) : sig
  val dominates : t
end = struct
  open M

  let dominates ~parent:a b = match resolve a, resolve b with
    | None, _ -> Label.(a <> b && a = pseudoentry)
    | _, None -> Label.(a <> b && b = pseudoexit)
    | Some `blk _, Some `blk _ ->
      Label.(a <> b) && is_descendant_of ~parent:a b
    | Some `insn (_, ba, _, _), Some `blk _ ->
      let a = Blk.label ba in
      Label.(a = b) || is_descendant_of ~parent:a b
    | Some `blk _, Some `insn (_, bb, _, _) ->
      let b = Blk.label bb in
      Label.(a <> b) && is_descendant_of ~parent:a b
    | Some `insn (_, ba, _, oa), Some `insn (_, bb, _, ob) ->
      let a = Blk.label ba in
      let b = Blk.label bb in
      if Label.(a = b) then oa < ob
      else is_descendant_of ~parent:a b
end
