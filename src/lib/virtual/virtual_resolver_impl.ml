open Core
open Monads.Std
open Regular.Std
open Resolver_intf

module E = Monad.Result.Error

open E.Let

module type L = sig
  type lhs

  module Insn : sig
    type t
    val label : t -> Label.t
    val lhs : t -> lhs
  end

  module Blk : sig
    type t
    val label : t -> Label.t
    val args : ?rev:bool -> t -> Var.t seq
    val insns : ?rev:bool -> t -> Insn.t seq
  end

  module Func : sig
    type t
    val blks : ?rev:bool -> t -> Blk.t seq
  end
end

module Make(M : L) : S
  with type lhs := M.lhs
   and type insn := M.Insn.t
   and type blk := M.Blk.t
   and type func := M.Func.t = struct
  open M

  type resolved = [
    | `blk  of Blk.t
    | `insn of Insn.t * Blk.t * lhs
  ]

  type t = {
    tbl  : resolved Label.Table.t;
    barg : Label.t Var.Table.t;
  }

  let resolve t = Hashtbl.find t.tbl
  let blk_arg t = Hashtbl.find t.barg

  let create fn =
    let tbl = Label.Table.create () in
    let barg = Var.Table.create () in
    let+ () = Func.blks fn |> E.Seq.iter ~f:(fun b ->
        let label = Blk.label b in
        let* () = match Hashtbl.add tbl ~key:label ~data:(`blk b) with
          | `Ok -> Ok ()
          | `Duplicate ->
            E.failf "Duplicate label for block %a" Label.pp label () in
        let* () = Blk.args b |> E.Seq.iter ~f:(fun x ->
            match Hashtbl.add barg ~key:x ~data:label with
            | `Ok -> Ok ()
            | `Duplicate ->
              E.failf "Duplicate label for block argument %a in block %a"
                Var.pp x Label.pp label ()) in
        Blk.insns b |> E.Seq.iter ~f:(fun i ->
            let key = Insn.label i in
            let data = `insn (i, b, Insn.lhs i) in
            match Hashtbl.add tbl ~key ~data with
            | `Ok -> Ok ()
            | `Duplicate ->
              E.failf "Duplicate label for instruction %a in block %a"
                Label.pp key Label.pp label ())) in
    {tbl; barg}
end
