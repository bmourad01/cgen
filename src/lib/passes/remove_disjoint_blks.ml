open Core
open Graphlib.Std
open Regular.Std

module type L = sig
  module Blk : sig
    type t
    val label : t -> Label.t
  end

  module Func : sig
    type t
    val entry : t -> Label.t
    val blks : ?rev:bool -> t -> Blk.t seq
    val remove_blks_exn : t -> Label.t list -> t
  end

  module Cfg : sig
    include Label.Graph_s
    val create : Func.t -> t
  end
end

module Make(M : L) = struct
  open M

  let reachable fn = with_return @@ fun {return} ->
    let cfg = Cfg.create fn in
    let start = Func.entry fn in
    Graphlib.depth_first_search (module Cfg) cfg ~start
      ~init:Label.Set.empty
      ~start_tree:(fun n s ->
          if Label.(n = start) then s else return s)
      ~enter_node:(fun _ n s -> Set.add s n)

  let run fn =
    Func.blks fn |> Seq.map ~f:Blk.label |>
    Seq.filter ~f:(Fn.non @@ Set.mem @@ reachable fn) |>
    Seq.to_list |> Func.remove_blks_exn fn
end

open Virtual

module V = Make(struct
    module Blk = Blk
    module Func = Func
    module Cfg = Cfg
  end)

module A = Make(struct
    module Blk = Abi.Blk
    module Func = Abi.Func
    module Cfg = Abi.Cfg
  end)

let run = V.run
let run_abi = A.run
