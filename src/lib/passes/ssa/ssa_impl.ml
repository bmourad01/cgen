open Core
open Regular.Std
open Graphlib.Std
open Ssa_impl_common

module Make(M : L) : sig
  val run : M.Func.t -> M.Func.t Or_error.t
  val check : M.Func.t -> unit Or_error.t
end = struct
  open M

  let init fn =
    let live = Live.compute fn in
    let cfg = Cfg.create fn in
    let dom = Graphlib.dominators (module Cfg) cfg Label.pseudoentry in
    let df = Graphlib.dom_frontier (module Cfg) cfg dom in
    let blks = Label.Table.create () in
    Func.blks fn |> Seq.iter ~f:(fun b ->
        Hashtbl.set blks ~key:(Blk.label b) ~data:b);
    {live; cfg; dom; df; blks}

  module Phi = Ssa_impl_phi.Make(M)
  module Rename = Ssa_impl_rename.Make(M)
  module Check = Ssa_impl_check.Make(M)

  let try_ fn f = try Ok (f ()) with
    | Missing_blk l ->
      Or_error.errorf
        "SSA: missing block %a in function $%s"
        Label.pps l (Func.name fn)
    | Invalid_argument msg | Failure msg ->
      Or_error.errorf "SSA: %s" msg

  let run fn = try_ fn @@ fun () ->
    if Dict.mem (Func.dict fn) Tags.ssa
    then fn
    else
      let env = init fn in
      Phi.go env;
      Rename.go env;
      let fn =
        Hashtbl.data env.blks |>
        Func.update_blks_exn fn in
      Check.go env.dom fn;
      Func.with_tag fn Tags.ssa ()

  let check fn = try_ fn @@ fun () ->
    let cfg = Cfg.create fn in
    let dom = Graphlib.dominators (module Cfg) cfg Label.pseudoentry in
    Check.go dom fn
end
