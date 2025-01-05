open Core
open Graphlib.Std
open Virtual.Abi

module P = Isel_internal.Pattern
module Id = Int

type id = Id.t [@@deriving compare, equal, hash, sexp]

type 'r node =
  | N of P.op * id list
  | Rv of 'r
[@@deriving compare, equal, hash, sexp]

type ty = [Type.basic | `flag | `v128]

type 'r t = {
  fn   : func;
  node : 'r node Vec.t;
  typs : ty Uopt.t Vec.t;
  cfg  : Cfg.t;
  dom  : Label.t tree;
  rpo  : Label.t -> int;
  blks : blk Label.Tree.t;
  vars : id Var.Table.t;
  insn : id Ftree.t Label.Table.t;
}

exception Missing_rpo of Label.t

let new_node ?l ?ty t n : id =
  let id = Vec.length t.node in
  assert (id = Vec.length t.typs);
  Vec.push t.node n;
  Vec.push t.typs @@ Uopt.of_option ty;
  Option.iter l ~f:(Hashtbl.update t.insn ~f:(function
      | Some ids -> Ftree.snoc ids id
      | None -> Ftree.singleton id));
  id

let typeof t id = Uopt.to_option @@ Vec.get_exn t.typs id
