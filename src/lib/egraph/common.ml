open Core
open Monads.Std
open Graphlib.Std
open Virtual

module Id = Id
module Enode = Enode
module Exp = Exp
module O = Monad.Option

type exp = Exp.t [@@deriving bin_io, compare, equal, sexp]
type id = Id.t [@@deriving compare, equal, hash, sexp]
type enode = Enode.t [@@deriving compare, equal, hash, sexp]
type nodes = (enode * id) Vec.t

let pp_exp = Exp.pp

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

type t = {
  input       : Input.t;
  uf          : Uf.t;
  memo        : (enode, id) Hashtbl.t;
  classes     : eclass Id.Table.t;
  pending     : nodes;
  analyses    : nodes;
  id2lbl      : Label.t Id.Table.t;
  lbl2id      : id Label.Table.t;
  mutable ver : int;
}

type egraph = t
type subst = id String.Map.t
type matches = (id * subst) Vec.t

let find t id = Uf.find t.uf id

let eclass t id =
  let id = find t id in
  Hashtbl.find_or_add t.classes id
    ~default:(fun () -> create_eclass id)

let data t id =
  find t id |> Hashtbl.find t.classes |>
  Option.bind ~f:(fun c -> c.data)

let dominates t = Tree.is_descendant_of t.input.dom

let merge_data c l r ~left ~right = match l, r with
  | Some l, Some r -> assert (equal_const l r); c.data <- Some l
  | Some l, None   -> c.data <- Some l; right ()
  | None,   Some r -> c.data <- Some r; left ()
  | None,   None   -> ()
[@@specialise]

(* The canonical form for merge operations should be biased towards
   node `a`, except when `b` is known to dominate it. *)
let merge_provenance ({id2lbl = p; _} as t) a b =
  match Hashtbl.(find p a, find p b) with
  | None, Some pb ->
    Hashtbl.set p ~key:a ~data:pb
  | Some pa, Some pb when dominates t ~parent:pb pa ->
    Hashtbl.set p ~key:a ~data:pb
  | Some pa, (Some _ | None) ->
    Hashtbl.set p ~key:b ~data:pa
  | None, None -> ()

(* Only update the mapping from IDs to labels.

   The mapping from labels to IDs only needs to be set once when
   we lift the CFG to the e-node representation. We can find the
   representative node for each label thanks to union-find.
*)
let update_provenance t id a =
  Hashtbl.update t.id2lbl id ~f:(function
      | Some b when dominates t ~parent:b a -> b
      | Some _ | None -> a)

let rec insert t n =
  let n = Enode.canonicalize n t.uf in
  find t @@ match Hashtbl.find t.memo n with
  | Some id -> id
  | None ->
    t.ver <- t.ver + 1;
    let id = Uf.fresh t.uf in
    let c = eclass t id in
    let x = n, id in
    Vec.push c.nodes n;
    Vec.push t.pending x;
    c.data <- Enode.eval n ~data:(data t);
    Enode.children n |> List.iter ~f:(fun ch ->
        Vec.push (eclass t ch).parents x);
    Hashtbl.set t.memo ~key:n ~data:id;
    modify_analysis t id;
    id

and merge t a b =
  let a = find t a in
  let b = find t b in
  if a <> b then
    (* Decide on the representative element. *)
    let ca = eclass t a in
    let cb = eclass t b in
    let a, b, ca, cb = if rank ca < rank cb
      then b, a, cb, ca else a, b, ca, cb in
    assert (a = Uf.union t.uf a b);
    assert (a = ca.id);
    t.ver <- t.ver + 1;
    Hashtbl.remove t.classes b;
    (* Perform the merge. *)
    Vec.append t.pending cb.parents;
    Vec.append ca.nodes cb.nodes;
    Vec.append ca.parents cb.parents;
    merge_data ca ca.data cb.data
      ~left:(fun () -> Vec.append t.analyses ca.parents)
      ~right:(fun () -> Vec.append t.analyses cb.parents);
    merge_provenance t a b;
    modify_analysis t a

and modify_analysis t id = data t id |> Option.iter ~f:(fun d ->
    merge t id @@ insert t @@ Enode.of_const d;
    Vec.filter_inplace (eclass t id).nodes ~f:Enode.is_const)

let next v f = Option.iter ~f @@ Vec.pop v [@@specialise]

let update_node t n =
  let n' = Enode.canonicalize n t.uf in
  if not @@ Enode.equal_children n n' then Hashtbl.remove t.memo n;
  n'

let rec update_nodes t = next t.pending @@ fun (n, cid) ->
  let n = update_node t n in
  Hashtbl.find_and_call t.memo n
    ~if_not_found:(fun key -> Hashtbl.set t.memo ~key ~data:cid)
    ~if_found:(fun id -> merge t id cid);
  update_nodes t

let rec update_analyses t = next t.analyses @@ fun (n, cid) ->
  let cid = find t cid in
  let d = Enode.eval n ~data:(data t) in
  let c = eclass t cid in
  assert (c.id = cid);
  merge_data c c.data d ~right:Fn.id ~left:(fun () ->
      Vec.append t.analyses c.parents;
      modify_analysis t cid);
  update_analyses t

let process_unions t =
  while not Vec.(is_empty t.pending && is_empty t.analyses) do
    update_nodes t;
    update_analyses t
  done

let rebuild_classes t = Hashtbl.iter t.classes ~f:(fun c ->
    Vec.map_inplace c.nodes ~f:(Fn.flip Enode.canonicalize t.uf);
    Vec.dedup_and_sort c.nodes ~compare:Enode.compare)

let repair t =
  process_unions t;
  rebuild_classes t
