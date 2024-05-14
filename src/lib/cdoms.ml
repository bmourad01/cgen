(* Construct the instruction-level dominator tree. *)

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
  val resolve : Label.t -> [`blk of Blk.t | `insn of Insn.t * Blk.t * lhs] option
end

module Make(M : L) : sig
  val dominates : t
end = struct
  open M

  let dominates ~parent:a b = match resolve a, resolve b with
    | None, _ -> Label.(a = pseudoentry)
    | _, None -> Label.(b = pseudoexit)
    | Some `blk _, Some `blk _ ->
      Label.(a = b) || is_descendant_of ~parent:a b
    | Some `insn (_, ba, _), Some `blk _ ->
      let a = Blk.label ba in
      Label.(a = b) || is_descendant_of ~parent:a b
    | Some `blk _, Some `insn (_, bb, _) ->
      let b = Blk.label bb in
      Label.(a <> b) && is_descendant_of ~parent:a b
    | Some `insn (ia, ba, _), Some `insn (ib, bb, _) ->
      let a = Blk.label ba in
      let b = Blk.label bb in
      if Label.(a = b) then
        let a = Insn.label ia in
        let b = Insn.label ib in
        Blk.insns ba |> Seq.fold_until
          ~init:false ~finish:Fn.id ~f:(fun f x ->
              if Insn.has_label x a then Stop true
              else if Insn.has_label x b then Stop f
              else Continue f)
      else is_descendant_of ~parent:a b
end
