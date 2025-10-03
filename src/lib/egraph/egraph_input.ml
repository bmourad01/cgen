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

module Phis = Phi_values.Make(struct
    type t = Operands.t [@@deriving equal]
    let one = Operands.singleton
    let join = Set.union
  end)

(* General information about the function we're translating. *)
type t = {
  fn   : func;                      (* The function itself. *)
  loop : loops;                     (* Loops analysis. *)
  reso : resolver;                  (* Labels to blocks/insns. *)
  cfg  : Cfg.t;                     (* The CFG. *)
  dom  : Label.t Semi_nca.tree;     (* Dominator tree. *)
  domd : int Label.Table.t;         (* Dominator tree depths. *)
  pdom : Label.t Semi_nca.tree;     (* Post-dominator tree. *)
  rdom : Dominance.t;               (* Fine-grained dominance relation. *)
  df   : Label.t Semi_nca.frontier; (* Dominance frontiers. *)
  lst  : Last_stores.t;             (* Last stores analysis. *)
  tenv : Typecheck.env;             (* Typing environment. *)
  phis : Phis.state;                (* Block argument value sets. *)
  rpo  : Label.t -> int;            (* Reverse post-order number. *)
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

let dom_depths dom =
  let t = Label.Table.create () in
  let q = Stack.singleton (Label.pseudoentry, 0) in
  Stack.until_empty q (fun (l, d) ->
      Hashtbl.set t ~key:l ~data:d;
      Semi_nca.Tree.children dom l |> Seq.iter ~f:(fun l' ->
          Stack.push q (l', d + 1)));
  t

let init_rpo cfg =
  let nums = Label.Table.create () in
  Graphlib.reverse_postorder_traverse
    ~start:Label.pseudoentry (module Cfg) cfg |>
  Seq.iteri ~f:(fun i l -> Hashtbl.set nums ~key:l ~data:i);
  Hashtbl.find_exn nums

let resolve_blk reso l =
  match Resolver.resolve reso l with
  | Some `blk b -> Some b
  | Some _ | None -> None

let init fn tenv =
  let+ reso = Resolver.create fn in
  let cfg = Cfg.create fn in
  let loop = Loops.analyze ~name:(Func.name fn) cfg in
  let dom = Semi_nca.compute (module Cfg) cfg Label.pseudoentry in
  let pdom = Semi_nca.compute (module Cfg) cfg Label.pseudoexit ~rev:true in
  let df = Semi_nca.frontier (module Cfg) cfg dom in
  let rdom = init_dom_relation reso dom in
  let lst = init_last_stores cfg reso in
  let domd = dom_depths dom in
  let phis = Phis.analyze ~blk:(resolve_blk reso) cfg in
  let rpo = init_rpo cfg in
  {fn; loop; reso; cfg; dom; domd; pdom; rdom; df; lst; tenv; phis; rpo}
