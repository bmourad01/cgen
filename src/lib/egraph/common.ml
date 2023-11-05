open Core
open Graphlib.Std

module Id = Id
module Enode = Enode

type id = Id.t [@@deriving bin_io, compare, equal, hash, sexp]
type enode = Enode.t
type subst = Subst.t

let empty_subst : subst = String.Map.empty

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

(* The actual e-graph data structure.

   Aside from the typical elements (i.e. our hash-consing of e-nodes
   and our union-find for canonicalization), we also have various
   tables that are keeping track of the relationship between an ID
   and its position (label) in the CFG representation.

   This gets a bit more complex when we want to perform optimizations
   related to code motion (e.g. LICM, CSE, hoisting, sinking), so that's
   what all the extra hash tables are for.

   See the [Prov], [Extractor_core], and [Extractor_cfg] modules for
   examples of how this information gets used.

   Regarding the [intv] mapping, this information is based on the
   intervals analysis performed on the function (part of [input]),
   but this information is not stable across all program points for
   a given ID and must be updated depending on the current position
   of the [Builder].
*)
type t = {
  input   : Input.t;                  (* Analyses about the function. *)
  classes : Uf.t;                     (* The union-find for all e-classes. *)
  node    : enode Vec.t;              (* All e-nodes, indexed by ID. *)
  memo    : (enode, id) Hashtbl.t;    (* The hash-cons for optimized terms. *)
  lmoved  : Id.Set.t Label.Table.t;   (* Set of IDs that were moved to a given label. *)
  imoved  : Label.Set.t Id.Table.t;   (* Set of labels that were moved for a given ID. *)
  imoved2 : Label.t Id.Table.t;       (* The label a given ID was moved to. *)
  licm    : Id.Hash_set.t;            (* IDs that were moved via LICM. *)
  id2lbl  : Label.t Id.Table.t;       (* Maps unmoved IDs to labels. *)
  lbl2id  : id Label.Table.t;         (* Maps labels to IDs. *)
  typs    : Type.t Id.Table.t;        (* Maps IDs to types. *)
  intv    : Bv_interval.t Id.Table.t; (* Maps IDs to BV intervals (not stable). *)
  fuel    : int;                      (* Maximum rewrite depth. *)
  rules   : rules;                    (* The table of rewrite rules. *)
}

type egraph = t

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
