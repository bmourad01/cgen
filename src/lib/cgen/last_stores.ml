(* Last stores dataflow analysis. *)

open Core

module Solution = Fixpoint.Solution

module type L = sig
  module Insn : sig
    type t
    val label : t -> Label.t
    val can_store : t -> bool
  end
  module Blk : sig
    type t
    val insns : ?rev:bool -> t -> Insn.t Sequence.t
  end
  val resolve : Label.t -> Blk.t
end

type state = Label.t option [@@deriving equal]
type t = state Solution.t

module Make(M : L) = struct
  open M
  module Cfg = Label.Graph

  let first_insn l = match Sequence.hd @@ Blk.insns @@ resolve l with
    | Some i -> Insn.label i
    | None -> l

  let transfer l init =
    resolve l |> Blk.insns |> Sequence.fold ~init ~f:(fun s i ->
        if Insn.can_store i then Some (Insn.label i) else s)

  let step visits l prev next =
    if visits <= 1 then next (* nothing known yet *)
    else match prev, next with
      | Some a, Some b when Label.(a = b) -> prev
      | None, None -> None
      | _ -> Some (first_insn l)

  let analyze cfg start =
    Fixpoint.run ~step ~start
      ~init:(Solution.create Label.Tree.empty None)
      ~equal:equal_state ~merge:Fn.const ~f:transfer @@
    Cfg.Node.remove Label.pseudoentry @@
    Cfg.Node.remove Label.pseudoexit cfg
end
