open Core
open Monads.Std
open Virtual

module Id = Id
module Enode = Enode
module Exp = Exp
module O = Monad.Option

type exp = Label.t Exp.t
[@@deriving compare, equal, sexp]

type id = Id.t
[@@deriving compare, equal, hash, sexp]

type enode = Enode.t
[@@deriving compare, equal, hash, sexp]

type nodes = (enode * id) Vec.t

let sort_and_dedup t ~compare =
  Vec.sort t ~compare;
  let prev = ref None in
  Vec.filter_inplace t ~f:(fun x -> match !prev with
      | Some y when compare x y = 0 -> false
      | Some _ | None -> prev := Some x; true)
[@@specialise]

type eclass = {
  id           : id;
  nodes        : enode Vec.t;
  parents      : nodes;
  mutable data : const option;
}

let create_eclass id = {
  id;
  nodes = Vec.create ();
  parents = Vec.create ();
  data = None;
}

let rank c = Vec.length c.parents

type dominance = parent:Label.t -> Label.t -> bool

type t = {
  uf          : Uf.t;
  nodes       : (enode, id) Hashtbl.t;
  classes     : eclass Id.Table.t;
  pending     : nodes;
  analyses    : nodes;
  provenance  : Label.t Id.Table.t;
  dominance   : dominance;
  mutable ver : int;
}

type egraph = t

let create ~dominance = {
  uf = Uf.create ();
  nodes = Hashtbl.create (module Enode);
  classes = Id.Table.create ();
  pending = Vec.create ();
  analyses = Vec.create ();
  provenance = Id.Table.create ();
  dominance;
  ver = 0;
}

type query =
  | V of string
  | Q of Enode.op * query list
[@@deriving compare, equal, sexp]

(* Substitute query variables with an e-class ID. *)
type subst = id String.Map.t

(* A callback for the rule. *)
type 'a callback = t -> id -> subst -> 'a

type formula =
  | Const of query
  | Cond of query * bool callback
  | Dyn of query option callback

type rule = {
  pre  : query;
  post : formula;
}

module Rule = struct
  type t = rule

  let var x = V x
  let exp o = Q (o, [])
  let (&) o q = Q (o, q)
  let (=>) pre post = {pre; post = Const post}
  let (=>?) pre post ~if_ = {pre; post = Cond (post, if_)}
  let (=>*) pre gen = {pre; post = Dyn gen}
end

let eclass t id = Hashtbl.find_or_add t.classes id
    ~default:(fun () -> create_eclass id)

let data t id =
  Hashtbl.find t.classes id |>
  Option.bind ~f:(fun c -> c.data)

let find' t id = Uf.find t.uf id

let find_exn t (id : id) =
  if id < 0 || id >= Vec.length t.uf
  then invalid_argf "Invalid id %d" id ()
  else find' t id

let find t id = Option.try_with @@ fun () -> find_exn t id

let provenance t id = Hashtbl.find t.provenance id

(* Maps e-class IDs to equivalent e-nodes. *)
type classes = enode Vec.t Id.Table.t

let eclasses t : classes =
  let r = Id.Table.create () in
  Hashtbl.iteri t.nodes ~f:(fun ~key:n ~data:id ->
      let id = find' t id in
      Vec.push (Hashtbl.find_or_add r id ~default:Vec.create) n);
  r

(* Node IDs and their substitutions. *)
type matches = (id * subst) Vec.t
