(* Construct the instruction-level dominator tree. *)

open Core
open Regular.Std
open Graphlib.Std

module type L = sig
  type lhs

  module Insn : sig
    type t
    val label : t -> Label.t
  end

  module Blk : sig
    type t
    val insns : ?rev:bool -> t -> Insn.t seq
  end

  module Func : sig
    type t
    val entry : t -> Label.t
  end

  module G : Label.Graph

  val resolve : Label.t -> [`blk of Blk.t | `insn of Insn.t * Blk.t * lhs] option
end

module Make(M : L) = struct
  open M

  module Pseudo = Label.Pseudo(G)

  let create fn dom =
    let accum b g l =
      Blk.insns ~rev:true b |>
      Seq.fold ~init:(g, l) ~f:(fun (g, l) i ->
          let next = Insn.label i in
          let e = G.Edge.create next l () in
          G.Edge.insert e g, next) in 
    let rec aux g l = match resolve l with
      | None when Label.is_pseudo l -> g, l
      | None | Some `insn _ -> assert false
      | Some `blk b ->
        let g, first = accum b g l in
        children g l, first
    and children g l =
      Tree.children dom l |> Seq.fold ~init:g ~f:(fun g c ->
          let g, first = aux g c in
          let e = G.Edge.create l first () in
          G.Edge.insert e g) in
    let entry = Func.entry fn in
    let g = fst @@ aux (G.Node.insert entry G.empty) entry in
    Graphlib.dominators (module G) (Pseudo.add g) Label.pseudoentry
end
