open Core
open Regular.Std
open Virtual.Abi
open Isel_common

let needs_stack_frame fn =
  (* Takes variadic args. *)
  Func.variadic fn ||
  (* Takes explicit stack parameters. *)
  Func.args fn |> Seq.exists ~f:(function
      | `stk _, _ -> true
      | _ -> false) ||
  (* Explicitly calls a function or requests a pointer
     to the stack parameters. *)
  Func.blks fn |> Seq.exists ~f:(fun b ->
      Blk.insns b |> Seq.exists ~f:(fun i ->
          match Insn.op i with
          | `call _ | `stkargs _ -> true
          | _ -> false))

module Make(M : Machine_intf.S)(C : Context_intf.S) = struct
  let create fn =
    let cfg = Cfg.create fn in {
      fn;
      node = Vec.create ();
      typs = Vec.create ();
      id2r = Vec.create ();
      cfg;
      dom = Semi_nca.compute (module Cfg) cfg Label.pseudoentry;
      blks = Func.map_of_blks fn;
      v2id = Var.Table.create ();
      insn = Label.Table.create ();
      extra = Label.Table.create ();
      frame = needs_stack_frame fn;
    }

  open C.Syntax

  module Builder = Isel_builder.Make(M)(C)
  module Match = Isel_match.Make(M)(C)

  let is_ssa fn = Dict.mem (Func.dict fn) Tags.ssa

  let run fn =
    let* () = C.unless (is_ssa fn) @@ fun () ->
      C.failf "In Isel.run: expected SSA form for function $%s"
        (Func.name fn) () in
    let t = create fn in
    let* () = Builder.run t in
    Match.run t
end
