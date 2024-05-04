open Monads.Std
open Graphlib.Std
open Virtual

module E = Monad.Result.Error

open E.Let

(* General information about the function we're translating. *)
type t = {
  fn   : func;             (* The function itself. *)
  loop : loops;            (* Loops analysis. *)
  reso : resolver;         (* Labels to blocks/insns. *)
  cfg  : Cfg.t;            (* The CFG. *)
  dom  : Label.t tree;     (* Dominator tree. *)
  pdom : Label.t tree;     (* Post-dominator tree. *)
  cdom : Label.t tree;     (* Instruction-level dominator tree. *)
  df   : Label.t frontier; (* Dominance frontiers. *)
  lst  : Last_stores.t;    (* Last stores analysis. *)
  tenv : Typecheck.env;    (* Typing environment. *)
}

let init_cdoms fn reso dom =
  let module Cdom = Cdoms.Make(struct
      type lhs = Var.t option
      module Insn = Insn
      module Blk = Blk
      module Func = Func
      module G = Cfg
      let resolve = Resolver.resolve reso
    end) in
  Cdom.create fn dom

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

let init fn tenv =
  let+ reso = Resolver.create fn in
  let loop = Loops.analyze fn in
  let cfg = Cfg.create fn in
  let dom = Graphlib.dominators (module Cfg) cfg Label.pseudoentry in
  let pdom = Graphlib.dominators (module Cfg) cfg Label.pseudoexit ~rev:true in
  let df = Graphlib.dom_frontier (module Cfg) cfg dom in
  let cdom = init_cdoms fn reso dom in
  let lst = init_last_stores fn cfg reso in
  {fn; loop; reso; cfg; dom; pdom; cdom; df; lst; tenv}
