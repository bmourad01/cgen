open Core
open Regular.Std
open Graphlib.Std
open Virtual.Abi

module P = Isel_internal.Pattern
module Id = Int

type id = Id.t [@@deriving compare, equal, hash, sexp]
type node = N of P.op * id list [@@deriving compare, equal, hash, sexp]

type t = {
  fn   : func;
  node : node Vec.t;
  typs : [Type.basic | `flag] Uopt.t Vec.t;
  cfg  : Cfg.t;
  dom  : Label.t tree;
  rpo  : Label.t -> int;
  blks : blk Label.Tree.t;
  word : Type.imm_base;
  vars : id Var.Table.t;
}

exception Missing_rpo of Label.t

let init_rpo cfg =
  let nums = Label.Table.create () in
  Graphlib.reverse_postorder_traverse
    ~start:Label.pseudoentry (module Cfg) cfg |>
  Seq.iteri ~f:(fun i l -> Hashtbl.set nums ~key:l ~data:i);
  fun l -> match Hashtbl.find nums l with
    | None -> raise @@ Missing_rpo l
    | Some i -> i

let create fn word =
  let cfg = Cfg.create fn in {
    fn;
    node = Vec.create ();
    typs = Vec.create ();
    cfg;
    dom = Graphlib.dominators (module Cfg) cfg Label.pseudoentry;
    rpo = init_rpo cfg;
    blks = Func.map_of_blks fn;
    word;
    vars = Var.Table.create ();
  }

let new_node ?ty t n : id =
  let i = Vec.length t.node in
  assert (i = Vec.length t.typs);
  Vec.push t.node n;
  Vec.push t.typs @@ Uopt.of_option ty;
  i

let typeof t id = Uopt.to_option @@ Vec.get_exn t.typs id
