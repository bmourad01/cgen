open Core
open Common
open Monads.Std

module O = Monad.Option

type prov =
  | Label of Label.t
  | Id of id

let pp_prov ppf = function
  | Label l -> Format.fprintf ppf "%a" Label.pp l
  | Id id -> Format.fprintf ppf "%d" id

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
  | E (p, op, []) ->
    Format.fprintf ppf "(%a %a)" pp_prov p Enode.pp_op op
  | E (p, op, args) ->
    let pp_sep ppf () = Format.fprintf ppf " " in
    Format.fprintf ppf "(%a %a %a)" pp_prov p Enode.pp_op op
      (Format.pp_print_list ~pp_sep pp_ext) args

let pps_ext () e = Format.asprintf "%a" pp_ext e

let has t id = Hashtbl.mem t.table @@ find t.eg id

let id_cost t id = match Hashtbl.find t.table @@ find t.eg id with
  | None -> failwithf "Couldn't calculate cost for node id %a" Id.pps id ()
  | Some (c, _) -> c

let has_cost t : enode -> bool = function
  | N (_, cs) -> List.for_all cs ~f:(has t)
  | U {pre; post} -> has t pre && has t post

open O.Let

let node_cost t n =
  let+ () = O.guard @@ has_cost t n in
  Enode.cost ~child:(id_cost t) n, n

let saturate t =
  let unsat = ref true in
  while !unsat do
    unsat := false;
    (* Explore newer nodes first. *)
    for i = Vec.length t.eg.node - 1 downto 0 do
      node t.eg i |> node_cost t |>
      Option.iter ~f:(fun ((x, _) as term) ->
          find t.eg i |> Hashtbl.update t.table ~f:(function
              | Some ((y, _) as prev) when x >= y -> prev
              | Some _ | None -> unsat := true; term))
    done
  done

let init eg =
  let t = {
    eg;
    table = Id.Table.create ();
    memo = Id.Table.create ();
  } in
  saturate t;
  t

let prov t id = match Hashtbl.find t.eg.id2lbl id with
  | Some l -> Label l
  | None -> Id id

let rec extract t id =
  let id = find t.eg id in
  match Hashtbl.find t.memo id with
  | Some _ as e -> e
  | None ->
    let* _, n = Hashtbl.find t.table id in
    match n with
    | N (op, cs) ->
      let+ cs = O.List.map cs ~f:(extract t) in
      let e = E (prov t id, op, cs) in
      Hashtbl.set t.memo ~key:id ~data:e;
      e
    | U {pre; post} ->
      let id = find t.eg pre in
      assert (id = find t.eg post);
      extract t id
