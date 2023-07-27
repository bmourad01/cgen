open Core
open Graphlib.Std

module Id = Id
module Enode = Enode
module Exp = Exp

type exp = Exp.t [@@deriving bin_io, compare, equal, sexp]
type id = Id.t [@@deriving bin_io, compare, equal, hash, sexp]
type enode = Enode.t

let pp_exp = Exp.pp

type t = {
  input   : Input.t;
  classes : Uf.t;
  node    : enode Vec.t;
  memo    : (enode, id) Hashtbl.t;
  lmoved  : Id.Set.t Label.Table.t;
  imoved  : Label.Set.t Id.Table.t;
  id2lbl  : Label.t Id.Table.t;
  lbl2id  : id Label.Table.t;
  fuel    : int;
}

type egraph = t
type subst = id String.Map.t
type 'a callback = egraph -> subst -> 'a

let empty_subst = String.Map.empty

type pattern =
  | V of string
  | P of Enode.op * pattern list
[@@deriving compare, equal, sexp]

type formula =
  | Static of pattern
  | Cond of pattern * bool callback
  | Dyn of pattern option callback

type rule = {
  pre  : pattern;
  post : formula;
}

let find t id = Uf.find t.classes id
let node t id = Vec.get_exn t.node id
let dominates t = Tree.is_descendant_of t.input.cdom
let const t id = Enode.const ~node:(node t) @@ node t id
let typeof_var t x = Typecheck.Env.typeof_var t.input.fn x t.input.tenv
