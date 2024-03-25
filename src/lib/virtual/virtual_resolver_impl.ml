open Core
open Monads.Std
open Regular.Std
open Resolver_intf

module E = Monad.Result.Error

open E.Let
open E.Syntax

module type L = sig
  type lhs

  val vars_of_lhs : lhs -> Var.t list

  module Insn : sig
    type t
    val label : t -> Label.t
    val lhs : t -> lhs
    val free_vars : t -> Var.Set.t
  end

  module Ctrl : sig
    type t
    val free_vars : t -> Var.Set.t
  end

  module Blk : sig
    type t
    val label : t -> Label.t
    val ctrl : t -> Ctrl.t
    val args : ?rev:bool -> t -> Var.t seq
    val insns : ?rev:bool -> t -> Insn.t seq
  end

  module Func : sig
    type t
    val args : ?rev:bool -> t -> Var.t seq
    val slots : ?rev:bool -> t -> Virtual_slot.t seq
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

  type def = [
    | resolved
    | `slot
    | `arg
    | `blkarg of Blk.t
  ]

  type t = {
    lbl : resolved Label.Table.t;
    use : resolved list Var.Table.t;
    def : def Var.Table.t;
  }

  let resolve t = Hashtbl.find t.lbl
  let def t = Hashtbl.find t.def
  let uses t x = Hashtbl.find t.use x |> Option.value ~default:[]

  let insert t x y ~err = match Hashtbl.add t ~key:x ~data:y with
    | `Duplicate -> err ()
    | `Ok -> !!()

  let duplicate_def = E.failf "Duplicate definition for var %a" Var.pp
  let duplicate_label = E.failf "Duplicate label %a" Label.pp

  let create fn =
    let lbl = Label.Table.create () in
    let use = Var.Table.create () in
    let def = Var.Table.create () in
    let* () = Func.args fn |> E.Seq.iter ~f:(fun a ->
        insert def a `arg ~err:(duplicate_def a)) in
    let* () = Func.slots fn |> E.Seq.iter ~f:(fun s ->
        let x = Virtual_slot.var s in
        insert def x `slot ~err:(duplicate_def x)) in
    let+ () = Func.blks fn |> E.Seq.iter ~f:(fun b ->
        let label = Blk.label b in
        let blk = `blk b in
        let* () = insert lbl label blk ~err:(duplicate_label label) in
        let* () = Blk.args b |> E.Seq.iter ~f:(fun x ->
            insert def x (`blkarg b) ~err:(duplicate_def x)) in
        let+ () = Blk.insns b |> E.Seq.iter ~f:(fun i ->
            let key = Insn.label i in
            let lhs = Insn.lhs i in
            let data = `insn (i, b, lhs) in
            let* () = insert lbl key data ~err:(duplicate_label key) in
            let+ () = vars_of_lhs lhs |> E.List.iter ~f:(fun x ->
                insert def x data ~err:(duplicate_def x)) in
            Insn.free_vars i |> Set.iter ~f:(fun key ->
                Hashtbl.add_multi use ~key ~data)) in
        Blk.ctrl b |> Ctrl.free_vars |> Set.iter ~f:(fun key ->
            Hashtbl.add_multi use ~key ~data:blk)) in
    {lbl; use; def}
end
