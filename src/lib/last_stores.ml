(* Last stores dataflow analysis. *)

open Core
open Regular.Std
open Graphlib.Std

module type S = sig
  module Insn : sig
    type t
    val label : t -> Label.t
    val can_store : t -> bool
  end

  module Blk : sig
    type t
    val insns : ?rev:bool -> t -> Insn.t seq
  end

  module Func : sig
    type t
    val entry : t -> Label.t
  end

  module Cfg : Label.Graph

  val resolve : Label.t -> [ `blk of Blk.t | `insn of Insn.t * Blk.t * Var.t option]
end

type state = Label.t option [@@deriving equal]
type t = (Label.t, state) Solution.t

module Make(M : S) = struct
  open M

  let first_insn l = match resolve l with
    | `insn _ -> assert false
    | `blk b -> match Seq.hd @@ Blk.insns b with
      | Some i -> Insn.label i
      | None -> l

  let init fn =
    Solution.create Label.(Map.singleton (Func.entry fn) None) None

  let transfer l init = match resolve l with
    | `insn _ -> assert false
    | `blk b -> Blk.insns b |> Seq.fold ~init ~f:(fun s i ->
        if Insn.can_store i then Some (Insn.label i) else s)

  let step _ l = Option.merge ~f:(fun a b ->
      if Label.(a = b) then a else first_insn l)

  let analyze fn cfg =
    Graphlib.fixpoint (module Cfg) ~step
      ~init:(init fn)
      ~equal:equal_state
      ~merge:Fn.const
      ~f:transfer @@
    Cfg.Node.remove Label.pseudoentry @@
    Cfg.Node.remove Label.pseudoexit cfg
end
