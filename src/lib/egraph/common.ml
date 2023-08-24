open Core
open Graphlib.Std

module Id = Id
module Enode = Enode
module Exp = Exp

type exp = Exp.t [@@deriving bin_io, compare, equal, sexp]
type id = Id.t [@@deriving bin_io, compare, equal, hash, sexp]
type enode = Enode.t
type subst = id String.Map.t

let empty_subst = String.Map.empty
let pp_exp = Exp.pp

type pattern =
  | V of string
  | P of Enode.op * pattern list
[@@deriving compare, equal, hash, sexp]

type t = {
  input   : Input.t;
  classes : Uf.t;
  node    : enode Vec.t;
  memo    : (enode, id) Hashtbl.t;
  lmoved  : Id.Set.t Label.Table.t;
  imoved  : Label.Set.t Id.Table.t;
  id2lbl  : Label.t Id.Table.t;
  lbl2id  : id Label.Table.t;
  typs    : Type.t Id.Table.t;
  fuel    : int;
}

and egraph = t
and 'a callback = t -> subst -> 'a

and formula =
  | Static of pattern
  | Cond of pattern * bool callback
  | Dyn of pattern option callback

and rule = {
  pre  : pattern;
  post : formula;
}

type rules = {
  ops  : (Enode.op, (pattern list * formula) list) Hashtbl.t;
  vars : formula list String.Table.t;
}

let create_table rules =
  let t = {
    ops = Hashtbl.create (module struct
        type t = Enode.op [@@deriving compare, hash, sexp]
      end);
    vars = String.Table.create ();
  } in
  List.iter rules ~f:(fun r -> match r.pre with
      | V x -> Hashtbl.add_multi t.vars ~key:x ~data:r.post
      | P (o, ps) -> Hashtbl.add_multi t.ops ~key:o ~data:(ps, r.post));
  t

let find t id = Uf.find t.classes id
let node t id = Vec.get_exn t.node id
let dominates t = Tree.is_descendant_of t.input.cdom
let const t id = Enode.const ~node:(node t) @@ node t id
let typeof t id = Hashtbl.find t.typs id

let typeof_var t x =
  Typecheck.Env.typeof_var t.input.fn x t.input.tenv |> Or_error.ok

let word t =
  (Target.word @@ Typecheck.Env.target t.input.tenv :> Type.t)
