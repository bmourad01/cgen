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
  moved   : Id.Set.t Label.Table.t;
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

(* Track the provenance between e-class IDs and labels in the CFG
   representation. *)
module Prov = struct
  (* Lowest common ancestor in the dominator tree. *)
  let rec lca t a b =
    let p = Tree.parent t.input.cdom in
    match p a, p b with
    | Some a, Some b when Label.(a = b) -> a
    | Some a, Some b -> lca t a b
    | None, _ | _, None ->
      (* The root is pseudoentry, which we should never reach. *)
      assert false

  (* Mark this label as having moved up in the dominator tree. *)
  let move t l id = Hashtbl.update t.moved l ~f:(function
      | None -> Id.Set.singleton id
      | Some s -> Set.add s id)

  (* Update when we union two nodes together. *)
  let merge ({id2lbl = p; _} as t) a b =
    if a <> b then match Hashtbl.(find p a, find p b) with
      | None, None -> ()
      | None, Some pb ->
        Hashtbl.set p ~key:a ~data:pb
      | Some pa, None ->
        Hashtbl.set p ~key:b ~data:pa
      | Some pa, Some pb when Label.(pa = pb) -> ()
      | Some pa, Some pb when dominates t ~parent:pb pa ->
        Hashtbl.set p ~key:a ~data:pb
      | Some pa, Some pb when dominates t ~parent:pa pb ->
        Hashtbl.set p ~key:b ~data:pa
      | Some pa, Some pb ->
        let c = lca t pa pb in
        Hashtbl.remove p a;
        Hashtbl.remove p b;
        move t c @@ find t a;
        move t c @@ find t b

  (* We've matched on a value that we already hash-consed, so
     figure out which label it should correspond to. *)
  let update t id a = match Hashtbl.find t.id2lbl id with
    | None -> Hashtbl.set t.id2lbl ~key:id ~data:a
    | Some b when Label.(b = a) -> ()
    | Some b when dominates t ~parent:b a -> ()
    | Some b when dominates t ~parent:a b ->
      Hashtbl.set t.id2lbl ~key:id ~data:a
    | Some b ->
      let c = lca t a b in
      let cid = find t id in
      Hashtbl.remove t.id2lbl id;
      Hashtbl.remove t.id2lbl cid;
      move t c cid
end

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
let subsume_const t n id =
  if not @@ Enode.is_const n then
    Enode.eval ~node:(node t) n |> O.map ~f:(fun c ->
        let k = Enode.of_const c in
        let c = Hashtbl.find_or_add t.memo k
            ~default:(fun () -> new_node t k) in
        Uf.union t.classes id c;
        Prov.merge t id c;
        c)
  else Some id

(* Represent the union of two e-classes with a "union" node. *)
let union t id oid =
  let u = new_node t @@ U {pre = id; post = oid} in
  Uf.union t.classes id oid;
  Uf.union t.classes id u;
  Prov.merge t id oid;
  Prov.merge t id u;
  u

(* Stop iterating when we find that we've optimized to a constant. *)
let step t id oid =
  let open Continue_or_stop in
  if id <> oid then match node t oid with
    | n when Enode.is_const n ->
      Uf.union t.classes id oid;
      Prov.merge t id oid;
      Stop oid
    | _ -> Continue (union t id oid)
  else Continue id

let rec insert ?(d = 0) ?l ~rules t n =
  canon t n |> Hashtbl.find_and_call t.memo
    ~if_found:(fun id ->
        Option.iter l ~f:(Prov.update t id);
        id)
    ~if_not_found:(fun k ->
        let id = new_node t n in
        Option.iter l ~f:(fun l ->
            Hashtbl.set t.id2lbl ~key:id ~data:l);
        let oid = optimize ~d ~rules t n id in
        Hashtbl.set t.memo ~key:k ~data:oid;
        oid)

and optimize ~d ~rules t n id = match subsume_const t n id with
  | Some id -> id
  | None when d > t.fuel -> id
  | None ->
    search ~d:(d + 1) ~rules t id n |>
    Vec.fold_until ~init:id ~finish:Fn.id ~f:(step t)

and search ~d ~rules t id n =
  let m = Vec.create () in
  let u = Stack.create () in
  (* Match a constructor. *)
  let rec cons ?(env = empty_subst) p id (n : enode) = match p, n with
    | P (x,  _), N (y,  _) when not @@ Enode.equal_op x y -> None
    | P (_, xs), N (_, ys) -> children env xs ys
    | _, U {pre; post} -> union env p pre post
    | V x, N _ -> var env x id
  (* Explore the rewritten term first. In some cases, constant folding
     will run much faster if we keep rewriting it. If there's a match
     then we can enqueue the "original" term with the current state of
     the search for further exploration. *)
  and union env p pre post = match cls env post p with
    | Some _ as x -> Stack.push u (env, pre, p); x
    | None -> cls env pre p
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
      (* Explore the most recent rewrites first. *)
      cons r.pre id n |> Option.iter ~f:(app r.post);
      (* Then explore the "original" terms. *)
      while not @@ Stack.is_empty u do
        let env, id, p = Stack.pop_exn u in
        cls env id p |> Option.iter ~f:(app r.post);
      done);
  m

and apply ~d ~rules = function
  | Static q -> apply_static ~d ~rules q
  | Cond (q, k) -> apply_cond ~d ~rules q k
  | Dyn q -> apply_dyn ~d ~rules q

and apply_static ~d ~rules q t env = match q with
  | V x -> Map.find env x
  | P (o, ps) ->
    O.List.map ps ~f:(fun q -> apply_static ~d ~rules q t env) |>
    O.map ~f:(fun cs -> insert ~d ~rules t @@ N (o, cs))

and apply_cond ~d ~rules q k t env =
  if k t env then apply_static ~d ~rules q t env else None

and apply_dyn ~d ~rules q t env =
  q t env |> O.bind ~f:(fun q -> apply_static ~d ~rules q t env)
