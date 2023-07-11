open Core
open Common
open Monads.Std

module O = Monad.Option

type cost = child:(id -> int) -> enode -> int

type prov =
  | Label of Label.t
  | Id of id

(* We'll use an intermediate data structure for smoothing
   out the edges of translating to both the expression tree
   and CFG representations. *)
type ext = E of prov * Enode.op * ext list

type t = {
  eg          : egraph;
  cost        : cost;
  table       : (int * enode) Id.Table.t;
  memo        : ext Id.Table.t;
  mutable ver : int;
  mutable sat : bool;
}

let rec pp_ext ppf = function
  | E (_, op, args) ->
    let pp_sep ppf () = Format.fprintf ppf " " in
    Format.fprintf ppf "(%a %a)" Enode.pp_op op
      (Format.pp_print_list ~pp_sep pp_ext) args

let pps_ext () e = Format.asprintf "%a" pp_ext e

let init eg ~cost = {
  eg;
  cost;
  table = Id.Table.create ();
  memo = Id.Table.create ();
  ver = eg.ver;
  sat = false;
}

let id_cost t id = match Hashtbl.find t.table @@ find t.eg id with
  | None -> failwithf "Couldn't calculate cost for node id %a" Id.pps id ()
  | Some (c, _) -> c

let has_cost t n =
  Enode.children n |> List.for_all ~f:(Hashtbl.mem t.table)

let node_cost t n =
  if not @@ has_cost t n then None
  else Some (t.cost ~child:(id_cost t) n, n)

(* Find the least-expensive term. *)
let best_term t ns =
  Vec.fold ns ~init:None ~f:(fun acc n ->
      node_cost t n |> Option.merge acc
        ~f:(fun ((c1, _) as a) ((c2, _) as b) ->
            if c2 < c1 then b else a))

(* Saturate the cost table. *)
let rec saturate t =
  t.sat <- true;
  Hashtbl.iteri t.eg.classes ~f:(fun ~key:id ~data:c ->
      match Hashtbl.find t.table id, best_term t c.nodes with
      | None, Some term ->
        Hashtbl.set t.table ~key:id ~data:term;
        t.sat <- false
      | Some (x, _), Some ((y, _) as term) when y < x ->
        Hashtbl.set t.table ~key:id ~data:term;
        t.sat <- false
      | _ -> ());
  if not t.sat then saturate t

(* Check if the underlying e-graph has been updated. If so, we should
   re-compute the costs for each node. *)
let check t = if t.ver <> t.eg.ver then begin
    Hashtbl.clear t.table;
    Hashtbl.clear t.memo;
    t.ver <- t.eg.ver;
    t.sat <- false;
  end

(* Extract to our intermediate form and cache the results. *)
let rec extract_aux t id =
  let id = find t.eg id in
  match Hashtbl.find t.memo id with
  | Some _ as e -> e
  | None ->
    let open O.Let in
    let* _, n = Hashtbl.find t.table id in
    let+ cs = Enode.children n |> O.List.map ~f:(extract_aux t) in
    let p = match Hashtbl.find t.eg.id2lbl id with
      | Some l -> Label l
      | None -> Id id in
    let e = E (p, Enode.op n, cs) in
    Hashtbl.set t.memo ~key:id ~data:e;
    e

let extract t id =
  check t;
  if not t.sat then saturate t;
  extract_aux t id
