open Core
open Monads.Std
open Regular.Std
open Use_intf

module E = Monad.Result.Error

module type L = sig
  module Insn : sig
    type t
    val label : t -> Label.t
    val free_vars : t -> Var.Set.t
  end

  module Ctrl : sig
    type t
    val free_vars : t -> Var.Set.t
  end

  module Blk : sig
    type t
    val label : t -> Label.t
    val insns : ?rev:bool -> t -> Insn.t seq
    val ctrl : t -> Ctrl.t
  end

  module Func : sig
    type t
    val blks : ?rev:bool -> t -> Blk.t seq
  end
end

module Make(M : L) : S with type func := M.Func.t = struct
  open M

  type t = Label.Set.t Var.Map.t

  let find t x = match Var.Map.find t x with
    | None -> Label.Set.empty
    | Some uses -> uses

  let add_use l u x = Var.Map.update u x ~f:(function
      | None -> Label.Set.singleton l
      | Some s -> Set.add s l)

  let compute fn =
    Func.blks fn |> Seq.fold ~init:Var.Map.empty ~f:(fun init b ->
        let label = Blk.label b in
        let u = Blk.insns b |> Seq.fold ~init ~f:(fun init i ->
            let label = Insn.label i in
            Insn.free_vars i |> Set.fold ~init ~f:(add_use label)) in
        Blk.ctrl b |> Ctrl.free_vars |> Set.fold ~init:u ~f:(add_use label))            
end
