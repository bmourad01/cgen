open Core
open Regular.Std

module type L = sig
  module Blk : sig
    type t
    val label : t -> Label.t
  end

  module Func : sig
    type t
    val name : t -> string
    val blks : ?rev:bool -> t -> Blk.t seq
    val fold_reachable : t -> init:'a -> f:('a -> Blk.t -> 'a) -> 'a
    val remove_blks_exn : t -> Label.t list -> t
  end
end

module Make(M : L) = struct
  open M

  let run fn =
    let reachable =
      Func.fold_reachable fn ~init:Label.Tree_set.empty
        ~f:(fun s b -> Label.Tree_set.add s (Blk.label b)) in
    let blks =
      Func.blks fn |> Seq.map ~f:Blk.label |>
      Seq.filter ~f:(Fn.non @@ Label.Tree_set.mem reachable) |>
      Seq.to_list in
    List.iter blks ~f:(fun l ->
        Logs.debug (fun m ->
            m "%s: removing unreachable block %a in function %s"
              __FUNCTION__ Label.pp l (Func.name fn)));
    Func.remove_blks_exn fn blks
end

open Virtual

module V = Make(struct
    module Blk = Blk
    module Func = Func
  end)

module A = Make(struct
    module Blk = Abi.Blk
    module Func = Abi.Func
  end)

let run = V.run
let run_abi = A.run
