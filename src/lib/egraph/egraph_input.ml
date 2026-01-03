open Core
open Monads.Std
open Regular.Std
open Graphlib.Std
open Virtual

module E = Monad.Result.Error

open E.Let

module Operands = Set.Make(struct
    type t = operand [@@deriving compare, sexp]
  end)

module Phis_lang = struct
  module Ctrl = struct
    type t = ctrl
    let locals = (Phi_values.locals Ctrl.Table.enum :> t -> _)
  end
  module Blk = Blk
  module Func = Func
  module Cfg = Cfg
end

module Phis_domain = struct
  type t = Operands.t [@@deriving equal]
  let one = Operands.singleton
  let join = Set.union
end

module Phis = Phi_values.Make(Phis_lang)(Phis_domain)

(* General information about the function we're translating. *)
type t = {
  fn   : func;                  (* The function itself. *)
  loop : loops;                 (* Loops analysis. *)
  reso : resolver;              (* Labels to blocks/insns. *)
  cfg  : Cfg.t;                 (* The CFG. *)
  dom  : Label.t Semi_nca.tree; (* Dominator tree. *)
  pdom : Label.t Semi_nca.tree; (* Post-dominator tree. *)
  rdom : Dominance.t;           (* Fine-grained dominance relation. *)
  lst  : Last_stores.t;         (* Last stores analysis. *)
  tenv : Typecheck.env;         (* Typing environment. *)
  phis : Phis.state;            (* Block argument value sets. *)
  scc  : Label.t partition;     (* Strongly-connected components. *)
}

let init_dom_relation reso dom =
  let module Dom = Dominance.Make(struct
      type lhs = Var.t option
      type insn = Insn.t
      module Blk = Blk
      let is_descendant_of = Semi_nca.Tree.is_descendant_of dom
      let resolve = Resolver.resolve reso
    end) in
  Dom.dominates

let init_last_stores cfg reso =
  let module Lst = Last_stores.Make(struct
      module Insn = Insn
      module Blk = Blk
      module Cfg = Cfg
      let resolve l = match Resolver.resolve reso l with
        | Some `insn _ | None -> assert false
        | Some `blk b -> b
    end) in
  Lst.analyze cfg

let resolve_blk reso l =
  match Resolver.resolve reso l with
  | Some `blk b -> Some b
  | Some _ | None -> None

let init fn tenv =
  let+ reso = Resolver.create fn in
  let cfg = Cfg.create fn in
  let dom = Semi_nca.compute (module Cfg) cfg Label.pseudoentry in
  let loop = Loops.analyze ~dom ~name:(Func.name fn) cfg in
  let pdom = Semi_nca.compute (module Cfg) cfg Label.pseudoexit ~rev:true in
  let rdom = init_dom_relation reso dom in
  let lst = init_last_stores cfg reso in
  let phis = Phis.analyze ~blk:(resolve_blk reso) cfg in
  let scc = Graphlib.strong_components (module Cfg) cfg in
  Logs.debug (fun m ->
      m "%s: SCCs of $%s: %a%!"
        __FUNCTION__ (Func.name fn) (Partition.pp Label.pp) scc);
  {fn; loop; reso; cfg; dom; pdom; rdom; lst; tenv; phis; scc}
