open Core
open Monads.Std
open Regular.Std
open Graphlib.Std
open Virtual

module E = Monad.Result.Error
module G = Graphlib.Make(Label)(Unit)

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

module Pseudo = Label.Pseudo(G)

(* The "regular" dominator tree from the CFG is not fine-grained enough
   to work with our strategy for maintaining provenance in the e-graph.

   The tree should also include labels of instructions when considering
   the data-flow of the function.
*)
let cdoms fn reso dom =
  let accum b g l =
    Blk.insns ~rev:true b |>
    Seq.fold ~init:(g, l) ~f:(fun (g, l) i ->
        let next = Insn.label i in
        let e = G.Edge.create next l () in
        G.Edge.insert e g, next) in 
  let rec aux g l = match Resolver.resolve reso l with
    | None when Label.is_pseudo l -> g, l
    | None | Some `insn _ -> assert false
    | Some `blk b ->
      let g, first = accum b g l in
      children g l, first
  and children g l =
    Tree.children dom l |> Seq.fold ~init:g ~f:(fun g c ->
        let g, first = aux g c in
        let e = G.Edge.create l first () in
        G.Edge.insert e g) in
  let entry = Func.entry fn in
  let g = fst @@ aux (G.Node.insert entry G.empty) entry in
  Graphlib.dominators (module G) (Pseudo.add g) Label.pseudoentry

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
  let cdom = cdoms fn reso dom in
  let lst = init_last_stores fn cfg reso in
  {fn; loop; reso; cfg; dom; pdom; cdom; df; lst; tenv}
