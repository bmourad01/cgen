open Core
open Monads.Std
open Regular.Std
open Graphlib.Std
open Virtual

module E = Monad.Result.Error
module G = Graphlib.Make(Label)(Unit)

open E.Let

type resolved = [
  | `blk  of blk
  | `insn of insn * blk * Var.t option
]

(* General information about the function we're translating. *)
type t = {
  fn   : func;
  loop : loops;
  tbl  : resolved Label.Table.t;
  cfg  : Cfg.t;
  dom  : Label.t tree;
  pdom : Label.t tree;
  cdom : Label.t tree;
  df   : Label.t frontier;
  lst  : (Label.t, Label.t option) Solution.t;
  tenv : Typecheck.env;
  barg : Label.t Var.Table.t;
  intv : Intervals.t;
}

module Pseudo = Label.Pseudo(struct
    include G
    let e = ()
  end)

let create_tbl fn =
  let tbl = Label.Table.create () in
  let barg = Var.Table.create () in
  let+ () = Func.blks fn |> E.Seq.iter ~f:(fun b ->
      let label = Blk.label b in
      let* () = match Hashtbl.add tbl ~key:label ~data:(`blk b) with
        | `Ok -> Ok ()
        | `Duplicate ->
          E.failf "Duplicate label for block %a" Label.pp label () in
      let* () = Blk.args b |> E.Seq.iter ~f:(fun x ->
          match Hashtbl.add barg ~key:x ~data:label with
          | `Ok -> Ok ()
          | `Duplicate ->
            E.failf "Duplicate label for block argument %a in block %a"
              Var.pp x Label.pp label ()) in
      Blk.insns b |> E.Seq.iter ~f:(fun i ->
          let key = Insn.label i in
          let data = `insn (i, b, Insn.lhs i) in
          match Hashtbl.add tbl ~key ~data with
          | `Ok -> Ok ()
          | `Duplicate ->
            E.failf "Duplicate label for instruction %a in block %a"
              Label.pp key Label.pp label ())) in
  tbl, barg

(* The "regular" dominator tree from the CFG is not fine-grained enough
   to work with our strategy for maintaining provenance in the e-graph.

   The tree should also include labels of instructions when considering
   the data-flow of the function.
*)
let cdoms fn tbl dom =
  let accum b g l =
    Blk.insns ~rev:true b |> Seq.fold ~init:(g, l) ~f:(fun (g, l) i ->
        let next = Insn.label i in
        let e = G.Edge.create next l () in
        G.Edge.insert e g, next) in 
  let rec aux g l = match Hashtbl.find tbl l with
    | None when Label.is_pseudo l -> g, l
    | None | Some (`insn _) -> assert false
    | Some (`blk b) ->
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

module Last_stores = struct
  type state = Label.t option [@@deriving equal]

  let first_insn tbl l = match Hashtbl.find_exn tbl l with
    | `insn _ -> assert false
    | `blk b -> match Seq.hd @@ Blk.insns b with
      | Some i -> Insn.label i
      | None -> l

  let init fn =
    Solution.create Label.(Map.singleton (Func.entry fn) None) None

  let transfer tbl l init = match Hashtbl.find_exn tbl l with
    | `insn _ -> assert false
    | `blk b -> Blk.insns b |> Seq.fold ~init ~f:(fun s i ->
        if Insn.can_store i then Some (Insn.label i) else s)

  let step tbl _ l = Option.merge ~f:(fun a b ->
      if Label.(a = b) then a else first_insn tbl l)

  let analyze fn tbl cfg =
    Graphlib.fixpoint (module Cfg)
      ~init:(init fn)
      ~step:(step tbl)
      ~equal:equal_state
      ~merge:Fn.const
      ~f:(transfer tbl) @@
    Cfg.Node.remove Label.pseudoentry @@
    Cfg.Node.remove Label.pseudoexit cfg
end

let init fn tenv =
  let+ tbl, barg = create_tbl fn in
  let loop = Loops.analyze fn in
  let cfg = Cfg.create fn in
  let dom = Graphlib.dominators (module Cfg) cfg Label.pseudoentry in
  let pdom = Graphlib.dominators (module Cfg) cfg Label.pseudoexit ~rev:true in
  let df = Graphlib.dom_frontier (module Cfg) cfg dom in
  let cdom = cdoms fn tbl dom in
  let lst = Last_stores.analyze fn tbl cfg in
  let word = Target.word @@ Typecheck.Env.target tenv in
  let typeof x = match Typecheck.Env.typeof_var fn x tenv with
    | Error err -> failwith @@ Error.to_string_hum err
    | Ok t -> t in
  let intv = Intervals.analyze fn ~word ~typeof in
  {fn; loop; tbl; cfg; dom; pdom; cdom; df; lst; tenv; barg; intv}
