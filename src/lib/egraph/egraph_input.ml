open Core
open Monads.Std
open Regular.Std
open Graphlib.Std
open Virtual

module E = Monad.Result.Error

open E.Let

(* General information about the function we're translating. *)
type t = {
  fn   : func;              (* The function itself. *)
  loop : loops;             (* Loops analysis. *)
  reso : resolver;          (* Labels to blocks/insns. *)
  cfg  : Cfg.t;             (* The CFG. *)
  dom  : Label.t tree;      (* Dominator tree. *)
  domd : int Label.Table.t; (* Dominator tree depths. *)
  pdom : Label.t tree;      (* Post-dominator tree. *)
  cdom : Cdoms.t;           (* Instruction-level dominance relation. *)
  df   : Label.t frontier;  (* Dominance frontiers. *)
  lst  : Last_stores.t;     (* Last stores analysis. *)
  tenv : Typecheck.env;     (* Typing environment. *)
}

let init_cdoms reso dom =
  let module Cdom = Cdoms.Make(struct
      type lhs = Var.t option
      module Insn = Insn
      module Blk = Blk
      let rec is_descendant_of ~parent l = match Tree.parent dom l with
        | Some p -> Label.(p = parent) || is_descendant_of ~parent p
        | None -> false
      let resolve = Resolver.resolve reso
    end) in
  Cdom.dominates

let init_last_stores fn cfg reso =
  let module Lst = Last_stores.Make(struct
      module Insn = Insn
      module Blk = Blk
      module Func = Func
      module Cfg = Cfg
      let resolve l = match Resolver.resolve reso l with
        | Some `insn _ | None -> assert false
        | Some `blk b -> b
    end) in
  Lst.analyze fn cfg

let dom_depths dom =
  let t = Label.Table.create () in
  let q = Stack.singleton (Label.pseudoentry, 0) in
  Stack.until_empty q (fun (l, d) ->
      Hashtbl.set t ~key:l ~data:d;
      Tree.children dom l |> Seq.iter ~f:(fun l' ->
          Stack.push q (l', d + 1)));
  t

let init fn tenv =
  let+ reso = Resolver.create fn in
  let loop = Loops.analyze fn in
  let cfg = Cfg.create fn in
  let dom = Graphlib.dominators (module Cfg) cfg Label.pseudoentry in
  let pdom = Graphlib.dominators (module Cfg) cfg Label.pseudoexit ~rev:true in
  let df = Graphlib.dom_frontier (module Cfg) cfg dom in
  let cdom = init_cdoms reso dom in
  let lst = init_last_stores fn cfg reso in
  let domd = dom_depths dom in
  {fn; loop; reso; cfg; dom; domd; pdom; cdom; df; lst; tenv}
