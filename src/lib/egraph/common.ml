open Core
open Graphlib.Std

module Id = Id
module Enode = Enode

type id = Id.t [@@deriving bin_io, compare, equal, hash, sexp]
type enode = Enode.t
type subst = Subst.t

let empty_subst : subst = String.Map.empty

type t = {
  input   : Input.t;
  classes : Uf.t;
  node    : enode Vec.t;
  memo    : (enode, id) Hashtbl.t;
  lmoved  : Id.Set.t Label.Table.t;
  imoved  : Label.Set.t Id.Table.t;
  imoved2 : Label.t Id.Table.t;
  licm    : Id.Hash_set.t;
  id2lbl  : Label.t Id.Table.t;
  lbl2id  : id Label.Table.t;
  typs    : Type.t Id.Table.t;
  intv    : Bv_interval.t Id.Table.t;
  fuel    : int;
}

type egraph = t

type 'a callback = subst -> 'a

type pattern =
  | V of string
  | P of Enode.op * pattern list
[@@deriving compare, equal, hash, sexp]

type formula =
  | Static of pattern
  | Cond of pattern * bool callback
  | Dyn of pattern option callback

type rule = {
  pre  : pattern;
  post : formula;
}

type rules = (Enode.op, (pattern list * formula) list) Hashtbl.t

let create_table rules =
  let t = Hashtbl.create (module struct
      type t = Enode.op [@@deriving compare, hash, sexp]
    end) in
  List.iter rules ~f:(fun r -> match r.pre with
      | P (o, ps) -> Hashtbl.add_multi t ~key:o ~data:(ps, r.post)
      | V x ->
        (* Such rules are not really useful for anything and definitely
           will create soundness issues. *)
        invalid_argf "Cannot create a rule with a variable \
                      %s at the top-level" x ());
  t

let find t id = Uf.find t.classes id
let node t id = Vec.get_exn t.node id
let dominates t = Tree.is_descendant_of t.input.cdom
let const t id = Enode.const ~node:(node t) @@ node t id
let typeof t id = Hashtbl.find t.typs id
let interval t id = Hashtbl.find t.intv id

let typeof_var t x =
  Typecheck.Env.typeof_var t.input.fn x t.input.tenv |> Or_error.ok

let word t =
  (Target.word @@ Typecheck.Env.target t.input.tenv :> Type.t)

let wordsz t =
  Type.sizeof_imm_base @@
  Target.word @@
  Typecheck.Env.target t.input.tenv

let setty ?ty t id = Option.iter ty ~f:(fun ty ->
    Hashtbl.set t.typs ~key:id ~data:ty)

let setiv ?iv t id = Option.iter iv ~f:(fun iv ->
    Hashtbl.set t.intv ~key:id ~data:iv)
