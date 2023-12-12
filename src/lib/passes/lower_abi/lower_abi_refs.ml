open Core
open Regular.Std
open Lower_abi_common
open Virtual

open Context.Syntax

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
  | #operand as o -> oper o
  | `addr a -> `int (a, `i64)

(* An `unref` of an existing slot eliminates the need for
   us to create a new slot for it. *)
let is_slot env = function
  | `var x ->
    Func.slots env.fn |>
    Seq.exists ~f:(Fn.flip Slot.is_var x) |>
    Fn.flip Option.some_if x
  | _ -> None

let make_unref env x s a =
  if not @@ Hashtbl.mem env.refs x then
    let+ y = match is_slot env a with
      | Some y -> !!y
      | None ->
        let* k = type_cls env s in
        let* y = new_slot env k.size k.align in
        let* src, srci = match a with
          | `var x -> !!(x, [])
          | _ ->
            let+ x, i = Cv.Abi.unop (`copy `i64) (ref_oper a) in
            x, [i] in
        let+ blit = Cv.Abi.blit ~src:(`var src) ~dst:(`var y) `i64 k.size in
        Hashtbl.set env.unrefs ~key:x ~data:(srci @ blit);
        y in
    Hashtbl.set env.refs ~key:x ~data:y;
  else !!()

(* Turn struct refs into a minimal number of stack slots, such
   that the result of each `ref` and `unref` instruction is
   accounted for, as well as any `call` or `vaarg` instruction
   that may return a struct. *)
let canonicalize env = iter_blks env ~f:(fun b ->
    let* () =
      Blk.args b |> Context.Seq.iter ~f:(fun x ->
          typeof_var env x >>| function
          | #Type.compound ->
            Hashtbl.set env.refs ~key:x ~data:x
          | _ -> ()) in
    Blk.insns b |> Context.Seq.iter ~f:(fun i ->
        match Insn.op i with
        | `ref (x, `var y) -> make_ref env i b x y
        | `unref (x, s, a) -> make_unref env x s a
        | `vaarg (x, `name s, _)
        | `call (Some (x, `name s), _, _, _) ->
          let* k = type_cls env s in
          if k.size > 0 then
            let+ y = new_slot env k.size k.align in
            Hashtbl.set env.refs ~key:x ~data:y
          else !!()
        | _ -> !!()))
