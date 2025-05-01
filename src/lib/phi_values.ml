(* Dataflow analysis for the sets of values for block arguments. *)

open Core
open Regular.Std
open Graphlib.Std
open Virtual

module type Domain = sig
  type t [@@deriving equal]
  val one : operand -> t
  val join : t -> t -> t
end

module Make(D : Domain) = struct
  type state = D.t Var.Map.t [@@deriving equal]

  let local ~blk s : local -> state = function
    | `label (l, vs) ->
      blk l |> Option.value_map ~default:s ~f:(fun b ->
          let args = Seq.to_list @@ Blk.args b in
          match List.zip args vs with
          | Unequal_lengths -> assert false
          | Ok xs -> List.fold xs ~init:s ~f:(fun s (x, v) ->
              Map.update s x ~f:(function
                  | Some vs -> D.(join vs @@ one v)
                  | None -> D.one v)))

  let dst ~blk s : dst -> state = function
    | #local as l -> local ~blk s l
    | #global -> s

  let transfer ~blk l s =
    blk l |> Option.value_map ~default:s ~f:(fun b ->
        match Blk.ctrl b with
        | `hlt | `ret _ -> s
        | `jmp d -> dst ~blk s d
        | `br (_, y, n) ->
          dst ~blk (dst ~blk s y) n
        | `sw (_, _, d, tbl) ->
          let init = local ~blk s d in
          Ctrl.Table.enum tbl |> Seq.fold ~init
            ~f:(fun s (_, l') -> local ~blk s l'))

  let merge = Map.merge_skewed ~combine:(fun ~key:_ -> D.join)

  let analyze ~blk cfg =
    let init = Solution.create Label.Map.empty Var.Map.empty in
    let soln = Graphlib.fixpoint (module Cfg) cfg ~init ~merge
        ~equal:equal_state ~f:(transfer ~blk) in
    (* The pseudoexit label should have all of the accumulated
       results, since this is a forward-flow analysis. *)
    Solution.get soln Label.pseudoexit
end
