open Core
open Common
open Monads.Std

module O = Monad.Option

type prov =
  | Label of Label.t
  | Id of id

(* We'll use an intermediate data structure for smoothing
   out the edges of translating to both the expression tree
   and CFG representations. *)
type ext = E of prov * Enode.op * ext list

type t = {
  eg    : egraph;
  table : (int * enode) Id.Table.t;
  memo  : ext Id.Table.t;
}

let rec pp_ext ppf = function
  | E (_, op, []) ->
    Format.fprintf ppf "%a" Enode.pp_op op
  | E (_, op, args) ->
    let pp_sep ppf () = Format.fprintf ppf " " in
    Format.fprintf ppf "(%a %a)" Enode.pp_op op
      (Format.pp_print_list ~pp_sep pp_ext) args

let pps_ext () e = Format.asprintf "%a" pp_ext e

let has t id = Hashtbl.mem t.table @@ find t.eg id

let id_cost t id = match Hashtbl.find t.table @@ find t.eg id with
  | None -> failwithf "Couldn't calculate cost for node id %a" Id.pps id ()
  | Some (c, _) -> c

let has_cost t : enode -> bool = function
  | N (_, cs) -> List.for_all cs ~f:(has t)
  | U (a, b) -> has t a && has t b

let node_cost t n =
  if not @@ has_cost t n then None
  else Some (Enode.cost ~child:(id_cost t) n, n)

let rec saturate t =
  Vec.foldi t.eg.node ~init:true ~f:(fun id sat n ->
      let id = find t.eg id in
      match Hashtbl.find t.table id, node_cost t n with
      | None, Some term ->
        Hashtbl.set t.table ~key:id ~data:term;
        false
      | Some (x, _), Some ((y, _) as term) when y < x ->
        Hashtbl.set t.table ~key:id ~data:term;
        false
      | _ -> sat) || saturate t

let init eg =
  let t = {
    eg;
    table = Id.Table.create ();
    memo = Id.Table.create ();
  } in
  assert (saturate t);
  t

let prov t id = match Hashtbl.find t.eg.id2lbl id with
  | Some l -> Label l
  | None -> Id id

let rec extract t id =
  let id = find t.eg id in
  match Hashtbl.find t.memo id with
  | Some _ as e -> e
  | None ->
    let open O.Let in
    let* _, n = Hashtbl.find t.table id in
    match n with
    | N (op, cs) ->
      let+ cs = O.List.map cs ~f:(extract t) in
      let e = E (prov t id, op, cs) in
      Hashtbl.set t.memo ~key:id ~data:e;
      e
    | U (a, b) ->
      let a = find t.eg a in
      assert (a = find t.eg b);
      extract t a
