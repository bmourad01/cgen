open Core
open Virtual

module I = Bv_interval
module Vtree = Var.Tree

type state = I.t Vtree.t [@@deriving equal]

let empty_state : state = Vtree.empty

let combine_state x y ~f =
  Vtree.merge x y ~f:(fun ~key:_ a b -> f a b)

let join_state = combine_state ~f:I.union
let meet_state = combine_state ~f:I.intersect

let invert_state s =
  Vtree.fold s ~init:Vtree.empty ~f:(fun ~key ~data acc ->
      Vtree.set acc ~key ~data:(I.inverse data))

(* In most cases we don't want to union with the previous
   state for `x`. *)
let update s x i = Vtree.set s ~key:x ~data:i

let update_union s x i = Vtree.update s x ~f:(function
    | Some i' -> I.union i i'
    | None -> i)

let find_var = Vtree.find
let enum_state s = Vtree.to_sequence s

module Edge = struct
  type t = Label.t * Label.t [@@deriving compare, hash, sexp_of]
end

type ctx = {
  insns  : state Label.Table.t;       (* Out states for each instruction. *)
  narrow : (Edge.t, state) Hashtbl.t; (* Per-edge narrowing constraints. *)
  cond   : state Var.Table.t;         (* State implied by each condition variable. *)
  blks   : blk Label.Tree.t;          (* Labels to blocks. *)
  word   : Type.imm_base;             (* Word size. *)
  typeof : Var.t -> Type.t;           (* Typing of variables. *)
  cycloc : int;                       (* Cyclomatic complexity. *)
  cfg    : Cfg.t;                     (* Control-flow graph *)
  mutable src : Label.t;              (* Current source block for narrowing. *)
}

let create_ctx cycloc ~blks ~word ~typeof ~cfg = {
  insns = Label.Table.create ();
  narrow = Hashtbl.create (module Edge);
  cond = Var.Table.create ();
  blks;
  word;
  typeof;
  cycloc;
  cfg;
  src = Label.pseudoentry;
}

let narrow ctx l x i =
  Hashtbl.update ctx.narrow (ctx.src, l) ~f:(function
      | None -> Vtree.singleton x i
      | Some s -> update_union s x i)

let sizeof x ctx = match ctx.typeof x with
  | #Type.basic as b -> Some (Type.sizeof_basic b)
  | #Type.compound -> None
  | `flag -> Some 1
