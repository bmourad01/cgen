(* Lowering of instructions that make use of variables that refer
   to compound types. *)

open Core
open Regular.Std
open Sysv_common
open Virtual

let collect_mem_rets env = match env.rmem with
  | None -> Var.Set.empty
  | Some _ ->
    Func.blks env.fn |>
    Seq.fold ~init:Var.Set.empty
      ~f:(fun acc b -> match Blk.ctrl b with
          | `ret Some `var x -> Set.add acc x
          | _ -> acc)

module Make(Context : Context_intf.S_virtual) = struct
  open Context.Syntax
  open Make0(Context)
  module Cv = Context.Virtual

  (* Here, we follow a naive strategy such that for each `%x = ld:t %y`,
     %x will get its own stack slot %s and we blit the contents of %y
     to it. Later, a reference to %x will be a dereference of %s (e.g.
     at a `ret` or `call`), whereas if %x is passed as a block arg,
     it will be passed by reference.

     This helps us to preserve the SSA property, even though we're
     demoting %x to a stack slot for now. The generated code should
     open opportunity for further optimizations (e.g. slot promotion,
     slot coalescing, store-to-load forwarding, SROA, etc).
  *)
  let make_load env mrs x s a =
    Context.unless (Hashtbl.mem env.refs x) @@ fun () ->
    let* k = type_cls env s in
    (* Re-use the implicit first parameter instead of allocating
       a new stack slot. *)
    let* y = match env.rmem with
      | Some y when Set.mem mrs x -> !!y
      | Some _ | None -> new_slot env k.size k.align in
    let* src, srci = match a with
      | `var x -> !!(x, [])
      | _ ->
        let+ x, i = Cv.Abi.unop (`copy `i64) a in
        x, [i] in
    let+ blit = Cv.Abi.blit ~src ~dst:y `i64 k.size in
    Hashtbl.set env.unrefs ~key:x ~data:(srci @ blit);
    Hashtbl.set env.refs ~key:x ~data:y

  let make_store env l s v a =
    let* k = type_cls env s in
    (* The stored value must be a var, anything else would have
       not type-checked. *)
    let src = match v with
      | `var x -> find_ref env x
      | _ -> assert false in
    let* dst, dsti = match a with
      | `var x -> !!(x, [])
      | _ ->
        let+ x, i = Cv.Abi.unop (`copy `i64) a in
        x, [i] in
    let+ blit = Cv.Abi.blit ~src ~dst `i64 k.size in
    Hashtbl.set env.blits ~key:l ~data:(dsti @ blit)

  let lower env =
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
            | `load (x, `name s, a) ->
              make_load env mrs x s a
            | `store (`name s, v, a) ->
              make_store env (Insn.label i) s v a
            | `vaarg (x, `name s, _)
            | `call (Some (x, `name s), _, _, _) ->
              let* k = type_cls env s in
              let+ y = new_slot env k.size k.align in
              Hashtbl.set env.refs ~key:x ~data:y
            | _ -> !!()))
end
