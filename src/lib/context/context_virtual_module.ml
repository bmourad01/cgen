open Regular.Std

module M = Context_state.M

open M.Syntax

let map_funs m ~f =
  Virtual.Module.funs m |> M.Seq.map ~f >>| fun funs ->
  Seq.to_list funs |> Virtual.Module.with_funs m
