(* Dataflow analysis for the sets of values for block arguments. *)

open Core
open Regular.Std
open Graphlib.Std

module type Domain = sig
  type t [@@deriving equal]
  val one : Virtual.operand -> t
  val join : t -> t -> t
end

module type L = sig
  module Ctrl : sig
    type t
    val locals : t -> (Label.t * Virtual.operand list) list
  end
  module Blk : sig
    type t
    val args : ?rev:bool -> t -> Var.t seq
    val ctrl : t -> Ctrl.t
  end
  module Func : sig
    type t
  end
  module Cfg : sig
    include Label.Graph_s
    val create : Func.t -> t
  end
end

module Make(M : L)(D : Domain) = struct
  open M

  type state = D.t Var.Map.t [@@deriving equal]

  let local ~blk s (l, vs) : state =
    blk l |> Option.value_map ~default:s ~f:(fun b ->
        let args = Seq.to_list @@ Blk.args b in
        match List.zip args vs with
        | Unequal_lengths -> assert false
        | Ok xs -> List.fold xs ~init:s ~f:(fun s (x, v) ->
            Map.update s x ~f:(function
                | Some vs -> D.(join vs @@ one v)
                | None -> D.one v)))

  let transfer ~blk l s =
    blk l |> Option.value_map ~default:s ~f:(fun b ->
        Blk.ctrl b |> Ctrl.locals |>
        List.fold ~init:s ~f:(local ~blk))

  let merge = Map.merge_skewed ~combine:(fun ~key:_ -> D.join)

  let analyze ~blk cfg =
    let init = Solution.create Label.Map.empty Var.Map.empty in
    let soln = Graphlib.fixpoint (module Cfg) cfg ~init ~merge
        ~equal:equal_state ~f:(transfer ~blk) in
    (* The pseudoexit label should have all of the accumulated
       results, since this is a forward-flow analysis. *)
    Solution.get soln Label.pseudoexit
end
