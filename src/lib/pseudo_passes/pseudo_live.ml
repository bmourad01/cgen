open Core
open Regular.Std
open Graphlib.Std
open Pseudo

module Make(M : Machine_intf.S) = struct
  module Rv = M.Regvar

  type tran = {
    defs : Rv.Set.t;
    uses : Rv.Set.t;
  }

  let empty_tran = {
    defs = Rv.Set.empty;
    uses = Rv.Set.empty;
  }

  let pp_vars ppf vars =
    Format.pp_print_list
      ~pp_sep:Format.pp_print_space
      Rv.pp ppf (Set.to_list vars)

  let pp_transfer ppf {uses; defs; _} =
    Format.fprintf ppf "(%a) / (%a)" pp_vars uses pp_vars defs

  let (++) = Set.union and (--) = Set.diff
  let apply {defs; uses; _} vars = vars -- defs ++ uses

  type t = {
    blks : tran Label.Tree.t;
    outs : (Label.t, Rv.Set.t) Solution.t;
  }

  let lookup blks n =
    Label.Tree.find blks n |>
    Option.value ~default:empty_tran

  let transfer blks n vars =
    if Label.is_pseudo n then vars else apply (lookup blks n) vars

  let outs t l = Solution.get t.outs l
  let ins  t l = transfer t.blks l @@ outs t l
  let defs t l = (lookup t.blks l).defs
  let uses t l = (lookup t.blks l).uses

  let fold t ~init ~f =
    Label.Tree.fold t.blks ~init ~f:(fun ~key:l ~data:trans init ->
        f init l @@ apply trans @@ outs t l)

  let blks t x = fold t ~init:Label.Tree_set.empty ~f:(fun blks l ins ->
      if Set.mem ins x then Label.Tree_set.add blks l else blks)

  let solution t = t.outs

  let pp ppf t =
    Format.pp_open_vbox ppf 0;
    fold t ~init:() ~f:(fun () l vars ->
        Format.fprintf ppf "@[<h>%a: @[<hov 2>(%a)@]@]@;"
          Label.pp l pp_vars vars);
    Format.pp_close_box ppf ()

  let blk_defs b =
    Blk.insns b |> Seq.fold ~init:Rv.Set.empty
      ~f:(fun acc i -> acc ++ M.Insn.writes (Insn.insn i))

  let update l trans ~f = Label.Tree.update_with trans l
      ~has:f ~nil:(fun () -> f empty_tran)

  let free_vars_of_blk b =
    let (++) = Set.union and (--) = Set.diff in
    let init = Rv.Set.empty in
    Blk.insns b ~rev:true |> Seq.fold ~init ~f:(fun inc i ->
        let insn = Insn.insn i in
        inc -- M.Insn.writes insn ++ M.Insn.reads insn)

  let block_transitions g blks =
    Label.Tree.fold blks ~init:Label.Tree.empty ~f:(fun ~key ~data:b fs ->
        Label.Tree.add_exn fs ~key ~data:{
          defs = blk_defs b;
          uses = free_vars_of_blk b;
        }) |> fun init ->
    Label.Tree.fold blks ~init ~f:(fun ~key ~data:_ init ->
        Cfg.Node.preds key g |>
        Seq.filter ~f:(Label.Tree.mem blks) |>
        Seq.fold ~init ~f:(fun fs p -> update p fs ~f:(fun x ->
            {x with defs = x.defs})))

  let init keep =
    let s = Label.(Map.singleton pseudoexit keep) in
    Solution.create s Rv.Set.empty

  let compute' ?(keep = Rv.Set.empty) g blks =
    let blks = block_transitions g blks in {
      blks;
      outs = Graphlib.fixpoint (module Cfg) g
          ~init:(init keep) ~rev:true
          ~start:Label.pseudoexit
          ~merge:Set.union
          ~equal:Rv.Set.equal
          ~f:(transfer blks);
    }

  let compute ?(keep = Rv.Set.empty) fn =
    let g = Cfg.create ~dests:M.Insn.dests fn in
    let blks = Func.map_of_blks fn in
    compute' ~keep g blks
end
