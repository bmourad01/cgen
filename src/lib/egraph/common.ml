open Core
open Monads.Std
open Graphlib.Std

module Id = Id
module Enode = Enode
module Exp = Exp
module O = Monad.Option

type exp = Exp.t [@@deriving bin_io, compare, equal, sexp]
type id = Id.t [@@deriving bin_io, compare, equal, hash, sexp]
type enode = Enode.t

let pp_exp = Exp.pp

type t = {
  input   : Input.t;
  classes : Uf.t;
  node    : enode Vec.t;
  memo    : (enode, id) Hashtbl.t;
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
  | Const of pattern
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

let merge_provenance ({id2lbl = p; _} as t) a b =
  match Hashtbl.(find p a, find p b) with
  | None, Some pb ->
    Hashtbl.set p ~key:a ~data:pb
  | Some pa, Some pb when dominates t ~parent:pb pa ->
    Hashtbl.set p ~key:a ~data:pb
  | Some pa, (Some _ | None) ->
    Hashtbl.set p ~key:b ~data:pa
  | None, None -> ()

let canon t : enode -> enode = function
  | N (_, []) as n -> n
  | N (op, cs) -> N (op, List.map cs ~f:(find t))
  | U _ -> assert false

let new_node t n =
  let id = Uf.fresh t.classes in
  Vec.push t.node n;
  assert (id = Vec.length t.node - 1);
  id

(* If the node is already normalized then don't bother searching
   for matches. *)
let subsume_const t c n id =
  let k = Enode.of_const c in
  if not @@ Enode.equal n k then
    let c = match Hashtbl.find t.memo k with
      | Some c -> c
      | None ->
        let id = new_node t k in
        Hashtbl.set t.memo ~key:k ~data:id;
        id in
    Uf.union t.classes id c;
    merge_provenance t id c;
    c
  else id

(* Represent the union of two e-classes with a "union" node. *)
let union t id oid =
  let u = new_node t @@ U (id, oid) in
  Uf.union t.classes id oid;
  Uf.union t.classes id u;
  merge_provenance t id oid;
  merge_provenance t id u;
  u

let rec insert ?(d = 0) ?l ~rules t n =
  let k = canon t n in
  match Hashtbl.find t.memo k with
  | Some id -> id
  | None ->
    let id = new_node t n in
    Option.iter l ~f:(fun l ->
        Hashtbl.set t.id2lbl ~key:id ~data:l);
    let oid = optimize ~d ~rules t n id in
    Hashtbl.set t.memo ~key:k ~data:oid;
    oid

and optimize ~d ~rules t n id = match Enode.eval ~node:(node t) n with
  | Some c -> subsume_const t c n id
  | None when d > t.fuel -> id
  | None ->
    search ~d:(d + 1) ~rules t id n |>
    Vec.fold ~init:id ~f:(fun id oid ->
        if id <> oid then union t id oid else id)

and search ~d ~rules t id n =
  let m = Vec.create () in
  let u = Stack.create () in
  (* Match a constructor. *)
  let rec cons ?(env = empty_subst) p id (n : enode) = match p, n with
    | P (x,  _), N (y,  _) when not @@ Enode.equal_op x y -> None
    | P (_, xs), N (_, ys) -> children env xs ys
    | _, U (a, b) -> union env p a b
    | V x, N _ -> var env x id
  (* Get the first matching e-class of the union, and enqueue the
     second one for further exploration later (if necessary). *)
  and union env p a b = match cls env a p with
    | Some _ as a -> Stack.push u (env, b, p); a
    | None -> cls env b p
  (* Match all the children of an e-node. *)
  and children init qs xs = match List.zip qs xs with
    | Ok l -> O.List.fold l ~init ~f:(fun env (q, x) -> cls env x q)
    | Unequal_lengths -> None
  (* Produce a substitution for the variable. *)
  and var env x id = match Map.find env x with
    | None -> Some (Map.set env ~key:x ~data:id)
    | Some id' -> Option.some_if (id = id') env
  (* Match an e-class. *)
  and cls env id = function
    | V x -> var env x id
    | P _ as q -> cons ~env q id @@ node t id in
  (* Apply a post-condition to the substitution. *)
  let app f env =
    apply ~d ~rules f t env |>
    Option.iter ~f:(Vec.push m) in
  (* Try matching with every rule. *)
  List.iter rules ~f:(fun r ->
      (* Try an arbitrary path, and then look at the pending unioned
         nodes for further matches. *)
      cons r.pre id n |> Option.iter ~f:(app r.post);
      while not @@ Stack.is_empty u do
        let env, id, p = Stack.pop_exn u in
        cls env id p |> Option.iter ~f:(app r.post);
      done);
  m

and apply ~d ~rules = function
  | Const q -> apply_const ~d ~rules q
  | Cond (q, k) -> apply_cond ~d ~rules q k
  | Dyn q -> apply_dyn ~d ~rules q

and apply_const ~d ~rules q t env = match q with
  | V x -> Map.find env x
  | P (o, q) ->
    O.List.map q ~f:(fun q -> apply_const ~d ~rules q t env) |>
    O.map ~f:(fun cs -> insert ~d ~rules t @@ N (o, cs))

and apply_cond ~d ~rules q k t env =
  if k t env then apply_const ~d ~rules q t env else None

and apply_dyn ~d ~rules q t env =
  q t env |> O.bind ~f:(fun q -> apply_const ~d ~rules q t env)
