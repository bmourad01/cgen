open Core
open Virtual

module I = Bv_interval

type state = I.t Var.Map.t [@@deriving equal, sexp]

let empty_state : state = Var.Map.empty

let join_state x y =
  Map.merge_skewed x y ~combine:(fun ~key:_ a b -> I.union a b)

let meet_state x y =
  Map.merge_skewed x y ~combine:(fun ~key:_ a b -> I.intersect a b)

let invert_state = Map.map ~f:I.inverse

(* In most cases we don't want to union with the previous
   state for `x`. *)
let update s x i = Map.set s ~key:x ~data:i

let update_union s x i = Map.update s x ~f:(function
    | Some i' -> I.union i i'
    | None -> i)

let find_var = Map.find
let enum_state s = Map.to_sequence s

type ctx = {
  insns  : state Label.Table.t; (* Out states for each instruction. *)
  narrow : state Label.Table.t; (* Incoming state constraints for each block. *)
  cond   : state Var.Table.t;   (* State implied by each condition variable. *)
  blks   : blk Label.Tree.t;    (* Labels to blocks. *)
  word   : Type.imm_base;       (* Word size. *)
  typeof : Var.t -> Type.t;     (* Typing of variables. *)
  cycloc : int;                 (* Cyclomatic complexity. *)
}

let create_ctx cycloc ~blks ~word ~typeof = {
  insns = Label.Table.create ();
  narrow = Label.Table.create ();
  cond = Var.Table.create ();
  blks;
  word;
  typeof;
  cycloc;
}

let narrow ctx l x i = Hashtbl.update ctx.narrow l ~f:(function
    | None -> Var.Map.singleton x i
    | Some s -> update_union s x i)

let sizeof x ctx = match ctx.typeof x with
  | #Type.basic as b -> Some (Type.sizeof_basic b)
  | #Type.compound -> None
  | `flag -> Some 1
