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
open Virtual
open Sccp_intervals_common

module Solution = Fixpoint.Solution
module Interp = Sccp_intervals_interp

let find_var = find_var

(* Widen interval `i` using program-derived thresholds.

   When a block arg's interval is still growing after a certain
   number of visits, we widen each bound toward the next threshold
   constant from comparisons in the program rather than jumping
   straight to full. This preserves precision for common loop
   patterns like `i < n` where `n` is a known constant.

   pre: `i` is not empty or full
*)
let widen_with_thresholds ctx x i =
  match find_var ctx.thresholds x with
  | Some t when I.contains t i -> t
  | _ -> I.create_full ~size:(I.size i)

(* Number of visits before threshold widening kicks in,
   and before we give up and go to full. *)
let widen_delay = 3
let widen_limit = widen_delay * 2

let step ctx visits l _ s =
  (* Widening for block args. *)
  match Ltree.find ctx.blks l with
  | None -> s
  | Some b ->
    if visits > widen_limit then
      (* Second widening pass: give up and go to full. *)
      Blk.fold_args b ~init:s ~f:(fun s x ->
          match sizeof x ctx with
          | Some size -> update s x @@ I.create_full ~size
          | None -> s)
    else if visits > widen_delay then
      (* First widening pass: use thresholds. *)
      Blk.fold_args b ~init:s ~f:(fun s x ->
          match find_var s x with
          | Some i when I.(is_full i || is_empty i) -> s
          | Some i -> update s x @@ widen_with_thresholds ctx x i
          | None -> s)
    else s

let edge ctx src dst s =
  match Hashtbl.find ctx.narrow (src, dst) with
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
  let init = Func.fold_slots fn ~init ~f:(fun s x ->
      let size = Type.sizeof_imm_base ctx.word in
      update s (Slot.var x) @@ I.create_full ~size) in
  Solution.create
    (Ltree.singleton Label.pseudoentry init)
    empty_state

let transfer ctx l s =
  ctx.src <- l;
  match Ltree.find ctx.blks l with
  | Some b -> Interp.interp_blk ctx s b
  | None -> s

type t = {
  insns : state Label.Table.t;
  input : state Solution.t;
}

let insn t l =
  Hashtbl.find t.insns l |>
  Option.value ~default:empty_state

let input t l = Solution.get t.input l

let analyze fn ~word ~typeof =
  if Dict.mem (Func.dict fn) Tags.ssa then
    let cfg = Cfg.create fn in
    let blks = Func.map_of_blks fn in
    let ctx = create_ctx ~blks ~word ~typeof ~cfg in
    let input = Fixpoint.run (module Cfg) cfg
        ~step:(step ctx)
        ~edge:(edge ctx)
        ~start:Label.pseudoentry
        ~init:(init_state ctx fn)
        ~equal:equal_state
        ~merge:join_state
        ~f:(transfer ctx) in
    {insns = ctx.insns; input}
  else
    invalid_argf
      "Intervals analysis: function $%s is not in SSA form"
      (Func.name fn) ()
