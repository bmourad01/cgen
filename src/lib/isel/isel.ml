open Core
open Regular.Std
open Graphlib.Std
open Virtual.Abi
open Isel_common

let init_rpo cfg =
  let nums = Label.Table.create () in
  Graphlib.reverse_postorder_traverse
    ~start:Label.pseudoentry (module Cfg) cfg |>
  Seq.iteri ~f:(fun i l -> Hashtbl.set nums ~key:l ~data:i);
  fun l -> match Hashtbl.find nums l with
    | None -> raise @@ Missing_rpo l
    | Some i -> i

module Make(M : Machine_intf.S)(C : Context_intf.S) = struct
  let create fn =
    let cfg = Cfg.create fn in {
      fn;
      node = Vec.create ();
      typs = Vec.create ();
      cfg;
      dom = Graphlib.dominators (module Cfg) cfg Label.pseudoentry;
      rpo = init_rpo cfg;
      blks = Func.map_of_blks fn;
      vars = Var.Table.create ();
      insn = Label.Table.create ();
    }

  open C.Syntax

  let run fn =
    if Dict.mem (Func.dict fn) Tags.ssa then
      let _t = create fn in
      let name = Func.name fn in
      let pfn = Pseudo.Func.create ~name ~blks:[] in
      !!pfn
    else
      C.failf
        "In Isel.run: expected SSA form for function $%s"
        (Func.name fn) ()
end
