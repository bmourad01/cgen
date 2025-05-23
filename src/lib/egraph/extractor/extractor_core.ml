open Core
open Egraph_common
open Monads.Std
open Virtual

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
  | Id of {canon : id; real : id}

let pp_prov ppf = function
  | Label l -> Format.fprintf ppf "%a" Label.pp l
  | Id {canon; real} -> Format.fprintf ppf "%d:%d" canon real

(* We'll use an intermediate data structure for smoothing
   out the edges of translating the CFG representation. *)
type ext = E of prov * Enode.op * ext list

(* Let the bottom N bits of the cost be the depth of a given
   term, and the remaining upper bits are the actual cost
   of the operation(s).

   This should favor shallower terms, which in practice lead
   to more favorable register pressure.
*)
module Cost : sig
  type t = private Int63.t
  val (<) : t -> t -> bool
  val pure : int -> t
  val incr : t -> t
  val add : t -> t -> t
end = struct
  include Int63

  let depth_bits = 12
  let depth_mask = pred (one lsl depth_bits)
  let opc_mask = lnot depth_mask

  let opc c = c lsr depth_bits
  let depth c = c land depth_mask
  let create o d = (o lsl depth_bits) lor (d land depth_mask)
  let pure o = of_int o lsl depth_bits

  (* Make sure the increment doesn't wrap around. *)
  let incr c =
    let d = depth c in
    (c land opc_mask) lor
    (if d = depth_mask then d else succ d)

  let add x y =
    let o = opc x + opc y in
    let d = max (depth x) (depth y) in
    create o d
end

type cost = Cost.t

type t = {
  eg     : egraph;
  table  : (cost * enode) Id.Table.t;
  memo   : ext Id.Table.t;
  impure : Id.Hash_set.t;
}

let rec pp_ext ppf = function
  | E (p, op, []) ->
    Format.fprintf ppf "(%a %a)" pp_prov p Enode.pp_op op
  | E (p, op, args) ->
    let pp_sep ppf () = Format.fprintf ppf " " in
    Format.fprintf ppf "(%a %a %a)" pp_prov p Enode.pp_op op
      (Format.pp_print_list ~pp_sep pp_ext) args

let op_cost : Enode.op -> cost = function
  | Oint (i, t) ->
    (* In practice, a negative constant might need some work to
       compute. *)
    let neg = Bv.(msb i mod modulus (Type.sizeof_imm t)) in
    Cost.pure @@ Bool.to_int neg
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
  | Ostore _
  | Otbl _
  | Ovaarg _
  | Ovastart _ -> Cost.pure 0
  | Obr | Ovar _ -> Cost.pure 2
  | Osw _ | Obinop #Insn.bitwise_binop | Ounop _ -> Cost.pure 3
  | Obinop (`div _ | `udiv _ | `rem _ | `urem _) -> Cost.pure 90
  | Obinop (`mul _) -> Cost.pure 42
  | Obinop (`mulh _ | `umulh _) -> Cost.pure 11
  | Obinop _ -> Cost.pure 4
  | Osel _ -> Cost.pure 8

(* Fill the table with the "best" terms for each e-class. *)
module Saturation : sig
  val go : t -> unit
end = struct
  let get t id = find t.eg id |> Hashtbl.find_exn t.table
  let set t id ~f = find t.eg id |> Hashtbl.update t.table ~f

  let cost t (n : enode) = match n with
    | N (op, []) -> op_cost op, n
    | N (op, children) ->
      let k = List.fold children ~init:(op_cost op)
          ~f:(fun k id -> Cost.add k @@ fst @@ get t id) in
      Cost.incr k, n
    | U {pre; post} ->
      (* Break ties by favoring the rewritten term. *)
      let pre, a = get t pre in
      let post, b = get t post in
      if Cost.(pre < post) then pre, a else post, b

  (* We're searching in a pseudo-topological order, so we shouldn't need
     a fixpoint loop.

     Note that because of this ordering, we can always eagerly break ties
     by using the newer term.
  *)
  let go t = Vec.iteri t.eg.node ~f:(fun id n ->
      let (x, _) as term = cost t n in
      set t id ~f:(function
          | Some ((y, _) as prev) when Cost.(y < x) -> prev
          | Some _ | None -> term))
end

let init eg =
  let t = {
    eg;
    table = Id.Table.create ();
    memo = Id.Table.create ();
    impure = Id.Hash_set.create ();
  } in
  Saturation.go t;
  t

let rec must_remain_fixed op args = match (op : Enode.op) with
  | Obr
  | Ojmp
  | Oret
  | Osw _
  | Ocall0 _
  | Ocall _
  | Oload _
  | Ostore _
  | Ovaarg _
  | Ovastart _ ->
    (* Control-flow and other side-effecting instructions must
       remain fixed. *)
    true
  | Obinop (`div #Type.imm | `udiv _ | `rem #Type.imm | `urem _) ->
    (* With division/remainder on integers where the RHS is a
       known non-zero constant, we can safely move it. Otherwise,
       there is a chance that the instruction will trap, which
       is an observable effect. *)
    begin match args with
      | [_; E (_, Oint (i, _), [])] -> Bv.(i = zero)
      | _ -> true
    end
  | Oset _ ->
    (* `Oset x` is a proxy for the actual operation, so we should
       verify that it is pure *)
    begin match args with
      | [E (_, op, args)] -> must_remain_fixed op args
      | _ -> assert false
    end
  | _ -> false

let prov t cid id op args =
  if must_remain_fixed op args then begin
    Hash_set.add t.impure cid;
    match Hashtbl.find t.eg.ilbl cid with
    | Some l -> Label l
    | None when id = cid -> Id {canon = cid; real = id}
    | None -> match Hashtbl.find t.eg.ilbl id with
      | None -> Id {canon = cid; real = id}
      | Some l -> Label l
  end else Id {canon = cid; real = id}

module O = Monad.Option

let rec extract t id =
  let cid = find t.eg id in
  match Hashtbl.find t.memo cid with
  | Some _ as e -> e
  | None ->
    let open O.Let in
    let* _, n = Hashtbl.find t.table cid in
    match n with
    | N (op, cs) ->
      let+ cs = O.List.map cs ~f:(extract t) in
      let e = E (prov t cid id op cs, op, cs) in
      Hashtbl.set t.memo ~key:cid ~data:e;
      e
    | U {pre; post} ->
      let id = find t.eg post in
      assert (id = find t.eg pre);
      extract t post
