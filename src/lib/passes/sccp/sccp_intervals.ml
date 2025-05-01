(* This analysis performs abstract interpretation in the usual
   Kildall fixpoint loop, where our abstract domain is contiguous
   intervals of bitvectors.

   This does not capture the semantics of floating point numbers,
   which would require its own abstract domain (likely orders of
   magnitude more complicated than BV intervals). Thus in most
   cases we settle for overapproximation.

   Additionally, we avoid modeling memory for now to keep things
   relatively simple.
*)

open Core
open Regular.Std
open Graphlib.Std
open Virtual
open Sccp_intervals_common

let find_var = find_var

module Interp = Sccp_intervals_interp

let step ctx visits l _ s =
  (* Widening for block args. *)
  let s = match Label.Tree.find ctx.blks l with
    | None -> s
    | Some b ->
      (* XXX: we need a better widening heuristic for back edges.
         Allowing extra rounds of iteration only to return the most
         general overapproximation seems like a waste (and indeed
         this could noticably slow down compile times). *)
      if visits > ctx.cycloc then
        Blk.args b |> Seq.fold ~init:s ~f:(fun s x ->
            match sizeof x ctx with
            | Some size -> update s x @@ I.create_full ~size
            | None -> s)
      else s in
  (* Narrowing for constraints. *)
  match Hashtbl.find ctx.narrow l with
  | Some s' -> meet_state s s'
  | None -> s

let init_state ctx fn =
  let init =
    Func.args fn |>
    Seq.filter_map ~f:(fun (x, t) -> match t with
        | #Type.basic -> Some x
        | `name _ -> None) |>
    Seq.fold ~init:empty_state ~f:(fun s x ->
        match sizeof x ctx with
        | Some size -> update s x @@ I.create_full ~size
        | None -> s) in
  let init =
    Func.slots fn |> Seq.fold ~init ~f:(fun s x ->
        let size = Type.sizeof_imm_base ctx.word in
        update s (Slot.var x) @@ I.create_full ~size) in
  Solution.create Label.(Map.singleton pseudoentry init) empty_state

let transfer ctx l s = match Label.Tree.find ctx.blks l with
  | Some b -> Interp.interp_blk ctx s b
  | None -> s

type t = {
  insns : state Label.Table.t;
  input : (Label.t, state) Solution.t;
}

let insn t l =
  Hashtbl.find t.insns l |>
  Option.value ~default:empty_state

let input t l = Solution.get t.input l

(* Cyclomatic complexity is the number of linearly independent
   paths in a CFG, denoted by the formula:

   M = E - N + 2P

   where E is the number of edges, N is the number of nodes,
   and P is the number of connected components. For our purposes,
   P is always 1.
*)
let cyclomatic_complexity cfg =
  let e = Cfg.number_of_edges cfg in
  let n = Cfg.number_of_nodes cfg in
  e - n + 2

let analyze ?steps fn ~word ~typeof =
  if Dict.mem (Func.dict fn) Tags.ssa then
    let cfg = Cfg.create fn in
    let blks = Func.map_of_blks fn in
    let cycloc = cyclomatic_complexity cfg in
    let ctx = create_ctx cycloc ~blks ~word ~typeof in
    let input = Graphlib.fixpoint (module Cfg) cfg ?steps
        ~step:(step ctx)
        ~init:(init_state ctx fn)
        ~equal:equal_state
        ~merge:join_state
        ~f:(transfer ctx) in
    {insns = ctx.insns; input}
  else
    invalid_argf
      "Intervals analysis: function $%s is not in SSA form"
      (Func.name fn) ()
