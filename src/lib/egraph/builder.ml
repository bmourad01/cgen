open Core
open Regular.Std
open Graphlib.Std
open Monads.Std
open Virtual
open Common

module E = Monad.Result.Error

exception Missing of Label.t
exception Duplicate of Var.t * Label.t

type mem = {
  lst  : Label.t;
  addr : id;
  ty   : Type.basic;
} [@@deriving bin_io, compare, equal, hash, sexp]

type st =
  | Undef
  | Value of id * Label.t

module Mem = Regular.Make(struct
    type t = mem [@@deriving bin_io, compare, equal, hash, sexp]
    let pp ppf t = Format.fprintf ppf "%a" Sexp.pp_hum @@ sexp_of_t t
    let module_name = Some "Cgen.Egraph.Builder.Mem"
    let version = "0.1"
  end)

type env = {
  rules       : rule list;
  vars        : id Var.Table.t;
  mems        : st Mem.Table.t;
  mutable lst : Label.t option;
}

let init rules = {
  rules;
  vars = Var.Table.create ();
  mems = Mem.Table.create ();
  lst = None;
}

let node ?l env eg op args = insert ?l ~rules:env.rules eg @@ N (op, args)
let atom env eg op = node env eg op []

let var env eg x = Hashtbl.find_or_add env.vars x
    ~default:(fun () -> atom env eg @@ Ovar x)

let operand env eg : operand -> id = function
  | #const as c -> insert ~rules:env.rules eg @@ Enode.of_const c
  | `var x -> var env eg x

let operands env eg = List.map ~f:(operand env eg)

let global env eg : global -> id = function
  | `addr a -> atom env eg @@ Oaddr a
  | `sym (s, o) -> atom env eg @@ Osym (s, o)
  | `var x -> var env eg x

let local env eg : local -> id = function
  | `label (l, args) -> node env eg (Olocal l) (operands env eg args)

let dst env eg : dst -> id = function
  | #global as g -> global env eg g
  | #local as l -> local env eg l

let table env eg tbl =
  Ctrl.Table.enum tbl |> Seq.map ~f:(fun (i, l) ->
      node env eg (Otbl i) [local env eg l]) |> Seq.to_list

let prov ?x ?(f = Fn.const) env eg l op args =
  let id = node ~l env eg op args in
  Option.iter x ~f:(fun x ->
      match Hashtbl.add env.vars ~key:x ~data:id with
      | `Duplicate -> raise @@ Duplicate (x, l)
      | `Ok -> ());
  Hashtbl.set eg.lbl2id ~key:l ~data:(f id eg)

let set env x id eg = node env eg (Oset x) [id]

let store env eg l ty v a =
  let v = operand env eg v in
  let a = operand env eg a in
  let key = {lst = l; addr = a; ty} in
  Hashtbl.set env.mems ~key ~data:(Value (v, l));
  prov env eg l (Ostore ty) [v; a];
  env.lst <- Some l

let alias env eg key l =
  Hashtbl.find env.mems key |>
  Option.bind ~f:(function
      | Undef -> None
      | Value (v, parent) ->
        Option.some_if (dominates eg ~parent l) v)

let load env eg l x ty a =
  let a = operand env eg a in
  let lst = Option.value env.lst ~default:l in
  let key = {lst; addr = a; ty} in
  match alias env eg key l with
  | Some v ->
    prov ~x env eg l (Ounop (`copy ty)) [v] ~f:(set env x)
  | None ->
    prov ~x env eg l (Oload (x, ty)) [a] ~f:(fun id _ ->
        Hashtbl.set env.mems ~key ~data:(Value (id, l));
        id)

let callop x : Enode.op * Var.t option = match x with
  | Some (x, t) -> Ocall (x, t), Some x
  | None -> Ocall0, None

let callargs env eg args =
  node env eg Ocallargs @@ operands env eg args

(* Our analysis is intraprocedural, so assume that a function call
   can do any arbitrary effects to memory. *)
let call env eg l x f args vargs =
  let op, x = callop x in
  env.lst <- Some l;
  prov ?x env eg l op [
    global env eg f;
    callargs env eg args;
    callargs env eg vargs;
  ]

(* Certain instructions such as variadic helpers have ABI-dependent
   or otherwise underspecified behaviors, which are not useful for
   removing redundant loads anyway. *)
let undef env lst addr ty =
  Hashtbl.set env.mems ~key:{lst; addr; ty} ~data:Undef;
  env.lst <- Some lst

let alist env eg : Insn.alist -> id = function
  | `var x -> var env eg x
  | `addr a -> atom env eg @@ Oaddr a
  | `sym (s, o) -> atom env eg @@ Osym (s, o)

let vaarg env eg l x ty a =
  ignore @@ var env eg x;
  let a = alist env eg a in
  undef env l a ty

let vastart env eg l x =
  let a = alist env eg x in
  let tgt = Typecheck.Env.target eg.input.tenv in
  let ty = (Target.word tgt :> Type.basic) in
  undef env l a ty

let insn env eg l : Insn.op -> unit = function
  | `bop (x, o, a, b) ->
    prov ~x env eg l (Obinop o) [
      operand env eg a;
      operand env eg b;
    ] ~f:(set env x)
  | `uop (x, o, a) ->
    prov ~x env eg l (Ounop o) [
      operand env eg a;
    ] ~f:(set env x)
  | `sel (x, ty, c, y, n) ->
    prov ~x env eg l (Osel ty) [
      var env eg c;
      operand env eg y;
      operand env eg n;
    ] ~f:(set env x)
  | `call (x, f, args, vargs) ->
    call env eg l x f args vargs
  | `alloc (x, _) ->
    ignore @@ var env eg x
  | `load (x, ty, a) ->
    load env eg l x ty a
  | `store (ty, v, a) ->
    store env eg l ty v a
  | `vaarg (x, ty, a) ->
    vaarg env eg l x ty a
  | `vastart x ->
    vastart env eg l x

let sw env eg l ty i d tbl =
  let i = operand env eg (i :> operand) in
  let d = local env eg d in
  let tbl = table env eg tbl in
  prov env eg l (Osw ty) (i :: d :: tbl)

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
    prov env eg l Oret [
      operand env eg r;
    ]
  | `sw (ty, i, d, tbl) ->
    sw env eg l ty i d tbl

let step env eg l = match Hashtbl.find eg.input.tbl l with
  | None when Label.is_pseudo l -> ()
  | None | Some `insn _ -> raise @@ Missing l
  | Some `blk b ->
    env.lst <- Hashtbl.find_exn eg.input.lst l;
    Blk.args b |> Seq.iter ~f:(fun (x, _) ->
        ignore @@ var env eg x);
    Blk.insns b |> Seq.iter ~f:(fun i ->
        insn env eg (Insn.label i) (Insn.op i));
    ctrl env eg l @@ Blk.ctrl b

let run eg rules =
  let env = init rules in
  let q = Stack.singleton Label.pseudoentry in
  let rec loop () = match Stack.pop q with
    | None -> Ok ()
    | Some l ->
      step env eg l;
      Tree.children eg.input.dom l |>
      Seq.iter ~f:(Stack.push q);
      loop () in
  try loop () with
  | Missing l ->
    E.failf "Missing block %a" Label.pp l ()
  | Duplicate (x, l) ->
    E.failf "Duplicate definition of var %a at instruction %a"
      Var.pp x Label.pp l ()
