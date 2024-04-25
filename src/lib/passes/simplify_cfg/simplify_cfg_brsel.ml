(* If we have an instruction:

   br %c, @5(%a, %b), @5(%x, %y)

   we turn this into:

   %0 = sel %c, %a, %x
   %1 = sel %c, %b, %y
   jmp @5(%0, %1)

   which can enable further simplifications,
   including getting rid of the `jmp` entirely.
*)

open Core
open Regular.Std
open Virtual
open Simplify_cfg_common

open Context.Syntax

exception Non_basic

let typeof tenv env fn x =
  match Typecheck.Env.typeof_var fn x tenv with
  | Ok t -> t
  | Error _ -> match Hashtbl.find env.typs x with
    | Some t -> t
    | None ->
      failwithf "variable %a in function $%s has no known type"
        Var.pps x (Func.name fn) ()

(* XXX: should `sel` support more than basic types? *)
let basicty tenv env fn x =  match typeof tenv env fn x with
  | #Type.basic as ty -> ty
  | _ -> raise_notrace Non_basic

let collect tenv env fn =
  Hashtbl.fold env.blks ~init:[] ~f:(fun ~key ~data:b acc ->
      try match Blk.ctrl b with
        | `br (c, `label (l, xs), `label (l', xs')) when Label.(l = l') ->
          let b' = Hashtbl.find_exn env.blks l in
          let typs =
            Blk.args b' |>
            Seq.map ~f:(basicty tenv env fn) |>
            Seq.to_list in
          let args = match List.map3 typs xs xs' ~f:Tuple3.create with
            | Ok args -> args
            | Unequal_lengths ->
              failwithf "in function $%s, block %a: incorrect arity in \
                         block arguments for `%s`"
                (Func.name fn) Label.pps key
                (Format.asprintf "%a" Ctrl.pp (Blk.ctrl b)) () in
          (b, c, l, args) :: acc
        | _ -> acc
      with Non_basic -> acc)

let run tenv env fn =
  collect tenv env fn |> Context.List.iter ~f:(fun (b, c, l, args) ->
      let+ sels = Context.List.map args ~f:(fun (ty, y, n) ->
          let+ x, sel = Context.Virtual.sel ty c y n in
          Hashtbl.set env.typs ~key:x ~data:(ty :> Type.t);
          `var x, sel) in
      let args, sels = List.unzip sels in
      let b = Blk.with_ctrl b @@ `jmp (`label (l, args)) in
      let b = Blk.append_insns b sels in
      Hashtbl.set env.blks ~key:(Blk.label b) ~data:b)
