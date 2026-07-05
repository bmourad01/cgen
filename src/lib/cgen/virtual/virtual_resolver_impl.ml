open Core
open Resolver_intf

module E = Cgen_utils.Monads.Error
module LT = Label.Dense_table
module VT = Var.Dense_table
module Vset = Var.Tree_set

module type L = sig
  type lhs

  val iter_vars_of_lhs : lhs -> f:(Var.t -> unit) -> unit

  module Insn : sig
    type t
    val label : t -> Label.t
    val lhs : t -> lhs
    val free_vars : t -> Vset.t
  end

  module Ctrl : sig
    type t
    val free_vars : t -> Vset.t
  end

  module Blk : sig
    type t
    val label : t -> Label.t
    val ctrl : t -> Ctrl.t
    val iter_args : ?rev:bool -> t -> f:(Var.t -> unit) -> unit
    val fold_insns : ?rev:bool -> t -> init:'a -> f:('a -> Insn.t -> 'a) -> 'a
  end

  module Func : sig
    type t
    val iter_args : ?rev:bool -> t -> f:(Var.t -> unit) -> unit
    val iter_slots : ?rev:bool -> t -> f:(Virtual_slot.t -> unit) -> unit
    val iter_reachable : t -> f:(Blk.t -> unit) -> unit
    val num_blks : t -> int
    val num_insns : t -> int
  end
end

exception Bad_use of Var.t
exception Duplicate_def of Var.t
exception Duplicate_label of Label.t

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
    else LT.set t ~key:x ~data:y

  let insert_var t x y ~err =
    if VT.mem t x then err ()
    else VT.set t ~key:x ~data:y

  let duplicate_def x () = raise_notrace @@ Duplicate_def x
  let duplicate_label l () = raise_notrace @@ Duplicate_label l

  let verify_uses use def =
    VT.iter_keys use ~f:(fun x ->
        if not @@ VT.mem def x then
          raise_notrace @@ Bad_use x)

  let uses_of fn vars =
    let use = VT.create ~capacity:(Vset.length vars) () in
    Func.iter_reachable fn ~f:(fun b ->
        let blk = `blk b in
        let _ =
          Blk.fold_insns b ~init:0 ~f:(fun ord i ->
              let data = `insn (i, b, Insn.lhs i, ord) in
              Insn.free_vars i |>
              Vset.inter vars |>
              Vset.iter ~f:(fun key ->
                  VT.add_multi use ~key ~data);
              ord + 1) in
        Blk.ctrl b |>
        Ctrl.free_vars |>
        Vset.inter vars |>
        Vset.iter ~f:(fun key ->
            VT.add_multi use ~key ~data:blk));
    fun x -> VT.find use x |> Option.value ~default:[]

  let create fn =
    try
      let nblk = Func.num_blks fn in
      let ninsn = Func.num_insns fn in
      let cap = nblk + ninsn in
      let lbl = LT.create ~capacity:cap () in
      let use = VT.create ~capacity:cap () in
      let def = VT.create ~capacity:cap () in
      Func.iter_args fn ~f:(fun a ->
          insert_var def a `arg ~err:(duplicate_def a));
      Func.iter_slots fn ~f:(fun s ->
          let x = Virtual_slot.var s in
          insert_var def x `slot ~err:(duplicate_def x));
      Func.iter_reachable fn ~f:(fun b ->
          let label = Blk.label b in
          let blk = `blk b in
          insert_lbl lbl label blk ~err:(duplicate_label label);
          Blk.iter_args b ~f:(fun x ->
              insert_var def x (`blkarg b) ~err:(duplicate_def x));
          let _ = Blk.fold_insns b ~init:0 ~f:(fun ord i ->
              let key = Insn.label i in
              let lhs = Insn.lhs i in
              let data = `insn (i, b, lhs, ord) in
              insert_lbl lbl key data ~err:(duplicate_label key);
              iter_vars_of_lhs lhs ~f:(fun x ->
                  insert_var def x data ~err:(duplicate_def x));
              Insn.free_vars i |> Vset.iter ~f:(fun key ->
                  VT.add_multi use ~key ~data);
              ord + 1) in
          Blk.ctrl b |> Ctrl.free_vars |> Vset.iter ~f:(fun key ->
              VT.add_multi use ~key ~data:blk));
      verify_uses use def;
      Ok {lbl; use; def}
    with
    | Bad_use x ->
      E.failf "Variable %a is used but not defined" Var.pp x ()
    | Duplicate_def x ->
      E.failf "Duplicate definition for var %a" Var.pp x ()
    | Duplicate_label l ->
      E.failf "Duplicate label %a" Label.pp l ()
end
