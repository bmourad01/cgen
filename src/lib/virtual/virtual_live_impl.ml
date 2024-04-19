open Core
open Graphlib.Std
open Regular.Std
open Live_intf

type tran = {
  defs  : Var.Set.t;
  uses  : Var.Set.t;
  insns : Var.Set.t Label.Tree.t;
}

let empty_tran = {
  defs  = Var.Set.empty;
  uses  = Var.Set.empty;
  insns = Label.Tree.empty;
}

let pp_vars ppf vars =
  Format.pp_print_list
    ~pp_sep:Format.pp_print_space
    Var.pp ppf (Set.to_list vars)

let pp_transfer ppf {uses; defs; _} =
  Format.fprintf ppf "(%a) / (%a)" pp_vars uses pp_vars defs

let (++) = Set.union and (--) = Set.diff
let apply {defs; uses; _} vars = vars -- defs ++ uses

module type L = sig
  module Insn : sig
    type t
    val lhs : t -> Var.Set.t
  end

  module Blk : sig
    type t
    val args : ?rev:bool -> t -> Var.t seq
    val insns : ?rev:bool -> t -> Insn.t seq
    val liveness : t -> Var.Set.t Label.Tree.t * Var.Set.t
  end

  module Func : sig
    type t
    val map_of_blks : t -> Blk.t Label.Tree.t
  end

  module Cfg : sig
    include Label.Graph
    val create : Func.t -> t
  end
end

module Make(M : L) : S with type func := M.Func.t = struct
  open M

  type t = {
    blks : tran Label.Tree.t;
    outs : (Label.t, Var.Set.t) Solution.t;
  }

  let lookup blks n =
    Label.Tree.find blks n |>
    Option.value ~default:empty_tran

  let transfer blks n vars =
    if Label.is_pseudo n then vars else apply (lookup blks n) vars

  let outs  t l = Solution.get t.outs l
  let ins   t l = transfer t.blks l @@ outs t l
  let defs  t l = (lookup t.blks l).defs
  let uses  t l = (lookup t.blks l).uses
  let insns t l = (lookup t.blks l).insns

  let fold t ~init ~f =
    Label.Tree.fold t.blks ~init ~f:(fun ~key:l ~data:trans init ->
        f init l @@ apply trans @@ outs t l)

  let blks t x = fold t ~init:Label.Set.empty ~f:(fun blks l ins ->
      if Set.mem ins x then Set.add blks l else blks)

  let solution t = t.outs

  let pp ppf t =
    Format.pp_open_vbox ppf 0;
    fold t ~init:() ~f:(fun () l vars ->
        Format.fprintf ppf "@[<h>%a: @[<hov 2>(%a)@]@]@;"
          Label.pp l pp_vars vars);
    Format.pp_close_box ppf ()

  let blk_defs b =
    Blk.insns b |> Seq.fold ~init:Var.Set.empty
      ~f:(fun acc i -> acc ++ Insn.lhs i)

  let update l trans ~f = Label.Tree.update_with trans l
      ~has:f ~nil:(fun () -> f empty_tran)

  let block_transitions g fn =
    let blks = Func.map_of_blks fn in
    Label.Tree.fold blks ~init:Label.Tree.empty ~f:(fun ~key ~data:b fs ->
        let insns, uses = Blk.liveness b in
        Label.Tree.add_exn fs ~key ~data:{
          defs = blk_defs b;
          uses;
          insns;
        }) |> fun init ->
    Label.Tree.fold blks ~init ~f:(fun ~key ~data:b init ->
        let args = Blk.args b |> Seq.fold ~init:Var.Set.empty ~f:Set.add in
        Cfg.Node.preds key g |>
        Seq.filter ~f:(Label.Tree.mem blks) |>
        Seq.fold ~init ~f:(fun fs p -> update p fs ~f:(fun x ->
            {x with defs = Set.union x.defs args})))

  let init keep =
    let s = Label.(Map.singleton pseudoexit keep) in
    Solution.create s Var.Set.empty

  let compute ?(keep = Var.Set.empty) fn =
    let g = Cfg.create fn in
    let blks = block_transitions g fn in {
      blks;
      outs = Graphlib.fixpoint (module Cfg) g
          ~init:(init keep) ~rev:true
          ~start:Label.pseudoexit
          ~merge:Set.union
          ~equal:Var.Set.equal
          ~f:(transfer blks);
    }
end
