open Core
open Monads.Std
open Regular.Std
open Resolver_intf

module E = Monad.Result.Error
module LT = Label.Dense_table
module VT = Var.Dense_table

open E.Let
open E.Syntax

module type L = sig
  type lhs

  val vars_of_lhs : lhs -> Var.t list

  module Insn : sig
    type t
    val label : t -> Label.t
    val lhs : t -> lhs
    val free_vars : t -> Var.Tree_set.t
  end

  module Ctrl : sig
    type t
    val free_vars : t -> Var.Tree_set.t
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
    val num_blks : t -> int
    val num_insns : t -> int
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
    | `insn of Insn.t * Blk.t * lhs * int
  ]

  type def = [
    | resolved
    | `slot
    | `arg
    | `blkarg of Blk.t
  ]

  type t = {
    lbl : resolved LT.t;
    use : resolved list VT.t;
    def : def VT.t;
  }

  let resolve t = LT.find t.lbl
  let def t = VT.find t.def
  let uses t x = VT.find t.use x |> Option.value ~default:[]

  let insert_lbl t x y ~err =
    if LT.mem t x then err ()
    else !!(LT.set t ~key:x ~data:y)

  let insert_var t x y ~err =
    if VT.mem t x then err ()
    else !!(VT.set t ~key:x ~data:y)

  let duplicate_def = E.failf "Duplicate definition for var %a" Var.pp
  let duplicate_label = E.failf "Duplicate label %a" Label.pp

  exception Bad_use of Var.t

  let verify_uses use def = try
      VT.iter_keys use ~f:(fun x ->
          if not @@ VT.mem def x then
            raise_notrace @@ Bad_use x);
      !!()
    with Bad_use x ->
      E.failf "Variable %a is used but not defined" Var.pp x ()

  let create fn =
    let nblk = Func.num_blks fn in
    let ninsn = Func.num_insns fn in
    let lbl = LT.create ~capacity:(nblk + ninsn) () in
    let use = VT.create () in
    let def = VT.create () in
    let* () = Func.args fn |> E.Seq.iter ~f:(fun a ->
        insert_var def a `arg ~err:(duplicate_def a)) in
    let* () = Func.slots fn |> E.Seq.iter ~f:(fun s ->
        let x = Virtual_slot.var s in
        insert_var def x `slot ~err:(duplicate_def x)) in
    let* () = Func.blks fn |> E.Seq.iter ~f:(fun b ->
        let label = Blk.label b in
        let blk = `blk b in
        let* () = insert_lbl lbl label blk ~err:(duplicate_label label) in
        let* () = Blk.args b |> E.Seq.iter ~f:(fun x ->
            insert_var def x (`blkarg b) ~err:(duplicate_def x)) in
        let+ _ = Blk.insns b |> E.Seq.fold ~init:0 ~f:(fun ord i ->
            let key = Insn.label i in
            let lhs = Insn.lhs i in
            let data = `insn (i, b, lhs, ord) in
            let* () = insert_lbl lbl key data ~err:(duplicate_label key) in
            let+ () = vars_of_lhs lhs |> E.List.iter ~f:(fun x ->
                insert_var def x data ~err:(duplicate_def x)) in
            Insn.free_vars i |> Var.Tree_set.iter ~f:(fun key ->
                VT.add_multi use ~key ~data);
            ord + 1) in
        Blk.ctrl b |> Ctrl.free_vars |> Var.Tree_set.iter ~f:(fun key ->
            VT.add_multi use ~key ~data:blk)) in
    let+ () = verify_uses use def in
    {lbl; use; def}
end
