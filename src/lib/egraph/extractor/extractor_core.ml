open Core
open Egraph_common
open Monads.Std
open Virtual

(* Keep track of the provenance of extracted nodes.

   We were previously using the real IDs for determining
   the order by which we place new instructions, but that
   is no longer guaranteed. In principle, lower IDs never
   depend on higher IDs to compute their results, but when
   we reschedule instructions in the CFG this is no longer
   useful.
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

(* Cost is packed into an Int63 with three fields, in order
   of significance:

   - opc: the operation cost of the term (dominates)
   - width: number of direct children that need registers (secondary)
   - depth: the depth of the term (tertiary tiebreaker)

   Constants and popular children (already materialized elsewhere)
   are excluded from width. This ordering means we first minimize
   total operations, then prefer terms with fewer simultaneously-live
   operands (less register pressure at the node), and finally prefer
   shallower terms.
*)
module Cost : sig
  type t = private Int63.t
  val (<) : t -> t -> bool
  val pure : int -> t
  val incr : width:int -> t -> t
  val accum : t -> t -> t
  val opc : t -> Int63.t
  val width : t -> Int63.t
  val depth : t -> Int63.t
  val pp : Format.formatter -> t -> unit
end = struct
  open Int63

  type nonrec t = t

  (* We want an unsigned comparison *)
  let compare_u a b = compare (a lxor min_value) (b lxor min_value) [@@inline]
  let (<) a b = Int.(compare_u a b < 0) [@@inline]

  let depth_bits = 8
  let width_bits = 8
  let low_bits = Int.(depth_bits + width_bits)
  let depth_mask = pred (one lsl depth_bits)
  let width_mask = pred (one lsl width_bits) lsl depth_bits
  let low_mask = pred (one lsl low_bits)

  let opc c = c lsr low_bits [@@inline]
  let width c = (c land width_mask) lsr depth_bits [@@inline]
  let depth c = c land depth_mask [@@inline]

  let create o w d =
    let o = o lsl low_bits in
    let w = (w land (pred one lsl width_bits)) lsl depth_bits in
    let d = d land depth_mask in
    o lor w lor d
  [@@inline]

  let pure o = of_int o lsl low_bits [@@inline]

  (* Finalize a compound node's cost with its width and depth. *)
  let incr ~width:w c =
    let d = depth c in
    let d = if d = depth_mask then d else succ d in
    let w = min (of_int w) (pred (one lsl width_bits)) in
    (c land (lnot low_mask)) lor (w lsl depth_bits) lor d
  [@@inline]

  let accum x y =
    let o = opc x + opc y in
    let d = max (depth x) (depth y) in
    create o zero d
  [@@inline]

  let pp = pp
end

type cost = Cost.t

type t = {
  eg             : egraph;
  table          : (cost * enode) Id.Table.t;
  safe           : (cost * enode) Id.Table.t;
  memo           : ext Id.Table.t;
  mutable impure : Bitset.t;
}

let rec pp_ext ppf = function
  | E (p, op, []) ->
    Format.fprintf ppf "(%a %a)" pp_prov p Enode.pp_op op
  | E (p, op, args) ->
    let pp_sep ppf () = Format.fprintf ppf " " in
    Format.fprintf ppf "(%a %a %a)" pp_prov p Enode.pp_op op
      (Format.pp_print_list ~pp_sep pp_ext) args

(* Pure cost of an operation.

   It's important to note that some of these costs are relative
   to what we can rewrite the operation into. For example,
   integer division/remainder has an enormous cost because we
   want to incentivize rewrites a la Hacker's Delight.
*)
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
  | Obinop (`div _ | `udiv _ | `rem _ | `urem _) -> Cost.pure 97
  | Obinop (`mul _) -> Cost.pure 42
  | Obinop (`mulh _ | `umulh _) -> Cost.pure 11
  | Obinop _ -> Cost.pure 4
  | Osel _ -> Cost.pure 8

(* Structural popularity: for each e-class, count how many distinct
   parent e-classes reference it as a child across all e-nodes.

   An e-class with popularity >= 2 is likely to be materialized
   regardless of extraction choices. Popular children are excluded
   from the width field so the secondary tiebreaker favors nodes
   whose operands are already live.
*)
let compute_popularity eg =
  let n = Vec.length eg.node in
  let seen1 = Array.create ~len:n (-1) in
  let popular = ref Bitset.empty in
  Vec.iteri eg.node ~f:(fun id -> function
      | N (Oset _, _) | U _ -> () (* skip signpost nodes *)
      | N (_, cs) ->
        let pid = find eg id in
        List.iter cs ~f:(fun cid ->
            let cid = find eg cid in
            if cid <> pid then
              let prev = seen1.(cid) in
              if prev < 0 then
                seen1.(cid) <- pid
              else if prev <> pid then
                popular := Bitset.set !popular cid));
  !popular

(* Fill the table with the "best" terms for each e-class. *)
module Saturation : sig
  val go : t -> unit
end = struct
  let get tbl eg id : cost * enode =
    Hashtbl.find_exn tbl @@ find eg id

  let cost tbl eg pop ~self (n : enode) = match n with
    | N (op, []) -> op_cost op, n
    | N (op, children) ->
      let width, k =
        List.fold children
          ~init:(0, op_cost op)
          ~f:(fun (w, k) id ->
              let cid = find eg id in
              let c, n = get tbl eg cid in
              (* Popular or constant children don't contribute to
                 register pressure. Exclude them from width. *)
              let pop_ok = cid <> self && Bitset.mem pop cid in
              let w = if pop_ok || Enode.is_const n then w else w + 1 in
              let k = Cost.accum k c in
              w, k) in
      Cost.incr ~width k, n
    | U {pre; post} ->
      let pre, a = get tbl eg pre in
      let post, b = get tbl eg post in
      if Cost.(pre < post) then pre, a else post, b

  (* We're searching in a pseudo-topological order, so we shouldn't need
     a fixpoint loop.

     Note that because of this ordering, we can always eagerly break ties
     by using the newer term.
  *)
  let saturate tbl eg pop =
    Vec.iteri eg.node ~f:(fun id n ->
        let self = find eg id in
        let (x, _) as term = cost tbl eg pop ~self n in
        let cid = self in
        Hashtbl.update tbl cid ~f:(function
            | Some ((y, _) as prev) when Cost.(y < x) -> prev
            | Some _ | None -> term))

  let go t =
    let pop = compute_popularity t.eg in
    (* First pass: undiscounted costs into safe table. *)
    saturate t.safe t.eg Bitset.empty;
    (* Second pass: popularity-aware costs into main table.
       Popular children still pay full opcode cost (avoiding
       cascade through decomposition chains), but are excluded
       from width so the secondary tiebreaker favors nodes
       whose operands are already materialized elsewhere. *)
    saturate t.table t.eg pop
end

let debug_dump t =
  let pp ppf (cid, (c, n)) =
    Format.fprintf ppf
      "  %d:\n    cost: %a (opc = %a, width = %a, depth = %a)\n    node: %a%!"
      cid Cost.pp c
      Int63.pp (Cost.opc c)
      Int63.pp (Cost.width c)
      Int63.pp (Cost.depth c)
      Enode.pp n in
  let sort l = List.sort l ~compare:(fun (a, _) (b, _) -> compare a b) in
  Logs.debug (fun m ->
      m "%s: $%s cost table:\n%a"
        __FUNCTION__ (Func.name t.eg.input.fn)
        (Format.pp_print_list pp
           ~pp_sep:(fun ppf () -> Format.fprintf ppf "\n"))
        (sort @@ Hashtbl.to_alist t.table);
      m "%s: $%s safe cost table:\n%a"
        __FUNCTION__ (Func.name t.eg.input.fn)
        (Format.pp_print_list pp
           ~pp_sep:(fun ppf () -> Format.fprintf ppf "\n"))
        (sort @@ Hashtbl.to_alist t.safe)
    )

let init eg =
  let t = {
    eg;
    table = Id.Table.create ();
    safe = Id.Table.create ();
    memo = Id.Table.create ();
    impure = Bitset.empty;
  } in
  Saturation.go t;
  debug_dump t;
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
  if must_remain_fixed op args then
    let () = t.impure <- Bitset.set t.impure cid in
    match labelof t.eg cid with
    | Some l -> Label l
    | None when id = cid -> Id {canon = cid; real = id}
    | None -> match labelof t.eg id with
      | None -> Id {canon = cid; real = id}
      | Some l -> Label l
  else Id {canon = cid; real = id}

module O = Monad.Option

let extract t =
  let rec go tbl visiting id =
    let cid = find t.eg id in
    match Hashtbl.find t.memo cid with
    | Some _ as e -> e
    | None when Bitset.mem visiting cid ->
      (* Cycle in discounted table: fall back to safe table,
         which is guaranteed acyclic (no discount). *)
      go t.safe Bitset.empty cid
    | None ->
      let visiting = Bitset.set visiting cid in
      let open O.Let in
      let* _, n = Hashtbl.find tbl cid in
      match n with
      | N (op, cs) ->
        let+ cs = O.List.map cs ~f:(go tbl visiting) in
        let e = E (prov t cid id op cs, op, cs) in
        Hashtbl.set t.memo ~key:cid ~data:e;
        e
      | U {pre; post} ->
        let id = find t.eg post in
        assert (id = find t.eg pre);
        go tbl visiting post in
  go t.table Bitset.empty
