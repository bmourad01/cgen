open Core
open Regular.Std
open Graphlib.Std
open Monads.Std
open Virtual
open Common

module E = Monad.Result.Error

exception Missing of Label.t
exception Duplicate of Var.t * Label.t

let node eg op args = insert eg @@ N (op, args)
let atom eg op = node eg op []

let var env eg x = Hashtbl.find_or_add env x
    ~default:(fun () -> atom eg @@ Ovar x)

let operand env eg : operand -> id = function
  | #const as c -> insert eg @@ Enode.of_const c
  | `var x -> var env eg x

let operands env eg = List.map ~f:(operand env eg)

let global env eg : global -> id = function
  | `addr a -> atom eg @@ Oaddr a
  | `sym s -> atom eg @@ Osym (s, 0)
  | `var x -> var env eg x

let local env eg : local -> id = function
  | `label (l, args) -> node eg (Olocal l) (operands env eg args)

let dst env eg : dst -> id = function
  | #global as g -> global env eg g
  | #local as l -> local env eg l

let table env eg tbl =
  Ctrl.Table.enum tbl |> Seq.map ~f:(fun (i, l) ->
      node eg (Otbl i) [local env eg l]) |> Seq.to_list

let prov ?x ?(f = Fn.const) env eg l op args =
  let id = node eg op args in
  Option.iter x ~f:(fun x ->
      match Hashtbl.add env ~key:x ~data:id with
      | `Duplicate -> raise @@ Duplicate (x, l)
      | `Ok -> ());
  update_provenance eg id l;
  Hashtbl.set eg.lbl2id ~key:l ~data:(f id eg)

let set x id eg = node eg (Oset x) [id]

let ctrl env eg l : ctrl -> unit = function
  | `hlt -> ()
  | `jmp d ->
    prov env eg l Ojmp [
      dst env eg d;
    ]
  | `br (c, y, n) ->
    prov env eg l Obr [
      var env eg c;
      dst env eg y;
      dst env eg n;
    ]
  | `ret None -> ()      
  | `ret (Some r) ->
    prov env eg l Oret [operand env eg r]
  | `sw (ty, i, d, tbl) ->
    let i = operand env eg (i :> operand) in
    let d = local env eg d in
    let tbl = table env eg tbl in
    prov env eg l (Osw ty) (i :: d :: tbl)

let callop x : Enode.op * Var.t option = match x with
  | Some (x, t) -> Ocall (x, t), Some x
  | None -> Ocall0, None

let callargs env eg args = node eg Ocallargs @@ operands env eg args

let insn env eg l : Insn.op -> unit = function
  | `bop (x, o, a, b) ->
    prov ~x env eg l (Obinop o) [
      operand env eg a;
      operand env eg b;
    ] ~f:(set x)
  | `uop (x, o, a) ->
    prov ~x env eg l (Ounop o) [
      operand env eg a;
    ] ~f:(set x)
  | `sel (x, ty, c, y, n) ->
    prov ~x env eg l (Osel ty) [
      var env eg c;
      operand env eg y;
      operand env eg n;
    ] ~f:(set x)
  | `call (x, f, args, vargs) ->
    let op, x = callop x in
    prov ?x env eg l op [
      global env eg f;
      callargs env eg args;
      callargs env eg vargs;
    ]
  | `alloc _ -> ()
  | `load (x, ty, a) ->
    prov ~x env eg l (Oload (x, ty)) [
      operand env eg a;
    ]
  | `store (ty, v, a) ->
    prov env eg l (Ostore ty) [
      operand env eg v;
      operand env eg a;
    ]
  | `vaarg _ -> ()
  | `vastart _ -> ()

let step env eg l = match Hashtbl.find eg.input.tbl l with
  | Some (`insn (i, _, _)) -> insn env eg l @@ Insn.op i
  | Some (`blk b) -> ctrl env eg l @@ Blk.ctrl b
  | None when Label.is_pseudo l -> ()
  | None -> raise @@ Missing l

let run eg =
  let env = Var.Table.create () in
  let q = Queue.singleton Label.pseudoentry in
  let rec loop () = match Queue.dequeue q with
    | None -> Ok ()
    | Some l ->
      step env eg l;
      Tree.children eg.input.dom l |>
      Seq.iter ~f:(Queue.enqueue q);
      loop () in
  try loop () with
  | Missing l ->
    E.failf "Missing instruction %a" Label.pp l ()
  | Duplicate (x, l) ->
    E.failf "Duplicate definition of var %a at instruction %a"
      Var.pp x Label.pp l ()
