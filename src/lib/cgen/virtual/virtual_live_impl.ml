open Core
open Regular.Std
open Live_intf

module Vset = Var.Tree_set
module Solution = Fixpoint.Solution

type tran = {
  defs : Vset.t;
  uses : Vset.t;
}

let empty_tran = {
  defs = Vset.empty;
  uses = Vset.empty;
}

let pp_vars ppf vars =
  Format.pp_print_list
    ~pp_sep:Format.pp_print_space
    Var.pp ppf (Vset.to_list vars)

let pp_transfer ppf {uses; defs; _} =
  Format.fprintf ppf "(%a) / (%a)" pp_vars uses pp_vars defs

let (++) = Vset.union and (--) = Vset.diff
let apply {defs; uses; _} vars = vars -- defs ++ uses

module type L = sig
  module Insn : sig
    type t
    val lhs : t -> Vset.t
  end

  module Blk : sig
    type t
    val free_vars : t -> Vset.t
    val has_any_args : t -> bool
    val fold_insns : ?rev:bool -> t -> init:'a -> f:('a -> Insn.t -> 'a) -> 'a
    val fold_args : ?rev:bool -> t -> init:'a -> f:('a -> Var.t -> 'a) -> 'a
  end

  module Func : sig
    type t
    val map_of_blks : t -> Blk.t Label.Tree.t
  end

  module Cfg : sig
    include Label.Graph_s
    val create : Func.t -> t
  end
end

module Make(M : L) : S
  with type var := Var.t
   and type var_set := Vset.t
   and type func := M.Func.t
   and type blk := M.Blk.t
   and type cfg := M.Cfg.t = struct
  open M

  type t = {
    blks : tran Label.Tree.t;
    outs : Vset.t Solution.t;
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
      if Vset.mem ins x then Label.Tree_set.add blks l else blks)

  let solution t = t.outs

  let pp ppf t =
    Format.pp_open_vbox ppf 0;
    fold t ~init:() ~f:(fun () l vars ->
        Format.fprintf ppf "@[<h>%a: @[<hov 2>(%a)@]@]@;"
          Label.pp l pp_vars vars);
    Format.pp_close_box ppf ()

  let blk_defs b =
    Blk.fold_insns b ~init:Vset.empty
      ~f:(fun acc i -> acc ++ Insn.lhs i)

  let update l trans ~f = Label.Tree.update_with trans l
      ~has:f ~nil:(fun () -> f empty_tran)

  let block_transitions g blks =
    Label.Tree.fold blks ~init:Label.Tree.empty ~f:(fun ~key ~data:b fs ->
        Label.Tree.add_exn fs ~key ~data:{
          defs = blk_defs b;
          uses = Blk.free_vars b;
        }) |> fun init ->
    Label.Tree.fold blks ~init ~f:(fun ~key ~data:b init ->
        if not (Blk.has_any_args b) then init else
          let args = Blk.fold_args b ~init:Vset.empty ~f:Vset.add in
          Cfg.Node.preds key g |>
          Seq.filter ~f:(Label.Tree.mem blks) |>
          Seq.fold ~init ~f:(fun fs p -> update p fs ~f:(fun x ->
              {x with defs = Vset.union x.defs args})))

  let init keep =
    Solution.create (Label.Tree.singleton Label.pseudoexit keep) Vset.empty

  let compute' ?(keep = Vset.empty) g blks =
    let blks = block_transitions g blks in {
      blks;
      outs = Fixpoint.run (module Cfg) g
          ~init:(init keep) ~rev:true
          ~start:Label.pseudoexit
          ~merge:Vset.union
          ~equal:Vset.equal
          ~f:(transfer blks);
    }

  let compute ?(keep = Vset.empty) fn =
    let g = Cfg.create fn in
    let blks = Func.map_of_blks fn in
    compute' ~keep g blks
end
