open Regular.Std

module M = Context_common.M

open M.Syntax

let map_funs m ~f =
  let+ funs = Virtual.Module.funs m |> M.Seq.map ~f in
  Seq.to_list funs |> Virtual.Module.with_funs m

let map_funs_abi m ~f =
  let+ funs = Virtual.Abi.Module.funs m |> M.Seq.map ~f in
  Seq.to_list funs |> Virtual.Abi.Module.with_funs m
