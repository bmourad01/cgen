open Core
open Regular.Std
open Sysv_common
open Virtual

open Context.Syntax

let collect_mem_rets env = match env.rmem with
  | None -> Var.Set.empty
  | Some _ ->
    Func.blks env.fn |>
    Seq.fold ~init:Var.Set.empty
      ~f:(fun acc b -> match Blk.ctrl b with
          | `ret Some `var x -> Set.add acc x
          | _ -> acc)

let make_ref env i b x y = match Hashtbl.find env.refs y with
  | Some z -> !!(Hashtbl.set env.canon_ref ~key:x ~data:z)
  | None -> typeof_var env y >>= function
    | `compound (s, _, _) | `opaque (s, _, _) ->
      let* k = type_cls env s in
      let*? s = Slot.create x ~size:k.size ~align:k.align in
      Hashtbl.set env.refs ~key:y ~data:x;
      Vec.push env.slots s;
      !!()
    | t ->
      Context.failf
        "Expected compound type for instruction %a \
         in block %a of function $%s, got %a"
        Insn.pp i Label.pp (Blk.label b)
        (Func.name env.fn) Type.pp t ()

let ref_oper = function
  | #operand as o -> o
  | `addr a -> `int (a, `i64)

(* The semantics for `unref` should be that we're dereferencing
   the address into a struct at the given point in time. Here, we
   follow a naive strategy such that for each `%x = unref :t %y`,
   %x will get its own stack slot %s and we blit the contents of %y
   to it. Later, a reference to %x will be a dereference of %s (e.g.
   at a `ret` or `call`), whereas if %x is passed as a block arg,
   it will be passed by reference.

   This helps us to preserve the SSA property, even though we're
   demoting %x to a stack slot for now. The generated code should
   open opportunity for further optimizations (e.g. slot promotion,
   slot coalescing, store-to-load forwarding, SROA, etc).
*)
let make_unref env mrs x s a =
  if not @@ Hashtbl.mem env.refs x then
    let* k = type_cls env s in
    (* Re-use the implicit first parameter instead of allocating
       a new stack slot. *)
    let* y = match env.rmem with
      | Some y when Set.mem mrs x -> !!y
      | Some _ | None -> new_slot env k.size k.align in
    let* src, srci = match a with
      | `var x ->
        (* There could be an existing slot for this ref *)
        let x = Option.value ~default:x @@
          Hashtbl.find env.canon_ref x in
        !!(x, [])
      | _ ->
        let+ x, i = Cv.Abi.unop (`copy `i64) (ref_oper a) in
        x, [i] in
    let+ blit = Cv.Abi.blit ~src ~dst:y `i64 k.size in
    Hashtbl.set env.unrefs ~key:x ~data:(srci @ blit);
    Hashtbl.set env.refs ~key:x ~data:y
  else !!()

(* Turn struct refs into a minimal number of stack slots, such
   that the result of each `ref` and `unref` instruction is
   accounted for, as well as any `call` or `vaarg` instruction
   that may return a struct. *)
let canonicalize env =
  let mrs = collect_mem_rets env in
  iter_blks env ~f:(fun b ->
      let* () =
        Blk.args b |> Context.Seq.iter ~f:(fun x ->
            typeof_var env x >>| function
            | #Type.compound ->
              Hashtbl.set env.refs ~key:x ~data:x
            | _ -> ()) in
      Blk.insns b |> Context.Seq.iter ~f:(fun i ->
          match Insn.op i with
          | `ref (x, `var y) -> make_ref env i b x y
          | `unref (x, s, a) -> make_unref env mrs x s a
          | `vaarg (x, `name s, _)
          | `call (Some (x, `name s), _, _, _) ->
            let* k = type_cls env s in
            let+ y = new_slot env k.size k.align in
            Hashtbl.set env.refs ~key:x ~data:y
          | _ -> !!()))
