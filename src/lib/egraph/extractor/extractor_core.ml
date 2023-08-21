open Core
open Common
open Monads.Std
open Virtual

module O = Monad.Option

(* We store the canonical and real IDs to help us determine
   the ordering when reifying back to the CFG representation.

   Canonical IDs help us extract the best term, but the real
   ID of the term determines the ordering; in particular, we
   order from oldest to newest. This makes sense since the way
   we build terms in the e-graph will be such that terms with
   a newer ID will always depend on an ID that is older.
*)
type prov =
  | Label of Label.t
  | Id of {canon: id; real: id}

let pp_prov ppf = function
  | Label l -> Format.fprintf ppf "%a" Label.pp l
  | Id {canon; real} -> Format.fprintf ppf "%d:%d" canon real

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

let cost t : enode -> int = function
  | N (op, children) ->
    let init = match op with
      | Oint (i, t) ->
        (* In practice, a negative constant might need some work to
           compute. *)
        Bool.to_int Bv.(msb i mod modulus (Type.sizeof_imm t))
      | Oaddr _
      | Obool _
      | Ocall0 _
      | Ocall _
      | Ocallargs
      | Odouble _
      | Ojmp
      | Oload _
      | Olocal _
      | Oret
      | Osingle _
      | Osym _
      | Oset _
      | Ostore _ -> 0
      | Obr | Otbl _ | Ovar _ -> 2
      | Osw _ | (Obinop #Insn.bitwise_binop) | Ounop _ -> 3
      | Obinop (`div _ | `udiv _ | `rem _ | `urem _) -> 90
      | Obinop (`mul _) -> 42
      | Obinop (`mulh _ | `umulh _) -> 11
      | Obinop _ -> 4
      | Osel _ -> 8 in
    List.fold children ~init ~f:(fun k c -> k + id_cost t c)
  | U {pre; post} -> min (id_cost t pre) (id_cost t post)

let node_cost t n =
  let+ () = O.guard @@ has_cost t n in
  cost t n, n

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

let prov t cid id = match Hashtbl.find t.eg.id2lbl cid with
  | Some l -> Label l
  | None -> match Hashtbl.find t.eg.id2lbl id with
    | None -> Id {canon = cid; real = id}
    | Some l -> Label l

let rec extract t id =
  let cid = find t.eg id in
  match Hashtbl.find t.memo cid with
  | Some _ as e -> e
  | None ->
    let* _, n = Hashtbl.find t.table cid in
    match n with
    | N (op, cs) ->
      let+ cs = O.List.map cs ~f:(extract t) in
      let e = E (prov t cid id, op, cs) in
      Hashtbl.set t.memo ~key:id ~data:e;
      e
    | U {pre; post} ->
      let id = find t.eg post in
      assert (id = find t.eg pre);
      extract t post
