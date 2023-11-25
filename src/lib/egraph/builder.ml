open Core
open Regular.Std
open Graphlib.Std
open Monads.Std
open Virtual
open Common

module E = Monad.Result.Error

exception Missing of Label.t
exception Duplicate of Var.t * Label.t

(* A key identifying a store to memory.

   [label]: the instruction that performed the access.

   [addr]: the ID of the value representing the address.

   [ty]: the type of value that was stored.
*)
type mem = {
  label : Label.t;
  addr  : id;
  ty    : Type.arg;
} [@@deriving bin_io, compare, equal, hash, sexp]

(* A value stored to memory.

   [Undef]: the value is undefined, but exists at the
   memory address.

   [Value (id, l)]: the value is defined by [id], and
   was stored (at least) by the instruction [l].
*)
type store =
  | Undef
  | Value of id * Label.t

module Mem = Regular.Make(struct
    type t = mem [@@deriving bin_io, compare, equal, hash, sexp]
    let pp ppf t = Format.fprintf ppf "%a" Sexp.pp_hum @@ sexp_of_t t
    let module_name = Some "Cgen.Egraph.Builder.Mem"
    let version = "0.1"
  end)

type env = {
  vars        : id Var.Table.t;    (* Remember the IDs for each SSA variable. *)
  mems        : store Mem.Table.t; (* Remember each memory access. *)
  mutable cur : Label.t;           (* Current instruction. *)
  mutable mem : Label.t option;    (* Most recent memory access. *)
}

let init () = {
  vars = Var.Table.create ();
  mems = Mem.Table.create ();
  cur = Label.pseudoentry;
  mem = None;
}

let node ?ty ?l eg op args =
  Rewrite.insert ?ty ?l ~d:eg.depth_limit eg @@ N (op, args)

let atom ?ty eg op = node ?ty eg op []

let constant ?ty eg k =
  Rewrite.insert ?ty ~d:eg.depth_limit eg @@ Enode.of_const k

let var env eg x =
  Hashtbl.find_or_add env.vars x ~default:(fun () ->
      let ty = typeof_var eg x in
      atom ?ty eg @@ Ovar x)

let typeof_const eg : const -> Type.t = function
  | `bool _ -> `flag
  | `int (_, t) -> (t :> Type.t)
  | `float _ -> `f32
  | `double _ -> `f64
  | `sym _ -> word eg

let operand env eg : operand -> id = function
  | #const as c ->
    let ty = typeof_const eg c in
    constant ~ty eg c
  | `var x -> var env eg x

let operands env eg = List.map ~f:(operand env eg)

let global env eg : global -> id = function
  | `addr a -> atom ~ty:(word eg) eg @@ Oaddr a
  | `sym (s, o) -> atom ~ty:(word eg) eg @@ Osym (s, o)
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
  let ty = Option.bind x ~f:(typeof_var eg) in
  let id = node ?ty ~l eg op args in
  Option.iter x ~f:(fun x ->
      match Hashtbl.add env.vars ~key:x ~data:id with
      | `Duplicate -> raise @@ Duplicate (x, l)
      | `Ok -> ());
  Hashtbl.set eg.lbl2id ~key:l ~data:(f id eg)

let set x id eg = node eg (Oset x) [id]

let store env eg l ty v a =
  let v = operand env eg v in
  let a = operand env eg a in
  let key = {
    label = l;
    addr = a;
    ty = (ty :> Type.arg)
  } in
  match ty with
  | `name _ -> assert false
  | #Type.basic as ty ->
    Hashtbl.set env.mems ~key ~data:(Value (v, l));
    prov env eg l (Ostore (ty, l)) [v; a];
    env.mem <- Some l

let alias env eg key l =
  Hashtbl.find env.mems key |>
  Option.bind ~f:(function
      | Undef -> None
      | Value (v, parent) ->
        Option.some_if (dominates eg ~parent l) v)

let load env eg l x ty a =
  let a = operand env eg a in
  (* The last memory access needs to be updated, even for a
     load, in order for redundant load elimination to work,
     since the `mem` keys expect a concrete label. *)
  let mem = match env.mem with
    | None -> env.mem <- Some l; l
    | Some l -> l in
  let key = {
    label = mem;
    addr = a;
    ty = (ty :> Type.arg)
  } in
  match alias env eg key l with
  | Some v ->
    prov ~x env eg l (Ounop (`copy ty)) [v] ~f:(set x)
  | None ->
    prov ~x env eg l (Oload (x, ty)) [a] ~f:(fun id _ ->
        Hashtbl.set env.mems ~key ~data:(Value (id, l));
        id)

let callop x l : Enode.op * Var.t option = match x with
  | Some (x, t) -> Ocall (x, t), Some x
  | None -> Ocall0 l, None

let callargs env eg args =
  node eg Ocallargs @@ operands env eg args

(* Our analysis is intraprocedural, so assume that a function call
   can do any arbitrary effects to memory. *)
let call env eg l x f args vargs =
  let op, x = callop x l in
  env.mem <- Some l;
  prov ?x env eg l op [
    global env eg f;
    callargs env eg args;
    callargs env eg vargs;
  ]

(* Certain instructions such as variadic helpers have ABI-dependent
   or otherwise underspecified behaviors, which are not useful for
   removing redundant loads anyway. *)
let undef env l addr ty =
  Hashtbl.set env.mems ~key:{
    label = l;
    addr;
    ty;
  } ~data:Undef;
  env.mem <- Some l

let vaarg env eg l x ty a =
  let a = global env eg a in
  undef env l a ty;
  prov ~x env eg l (Ovaarg (x, ty)) [a]

let vastart env eg l x =
  let a = global env eg x in
  let tgt = Typecheck.Env.target eg.input.tenv in
  let ty = (Target.word tgt :> Type.arg) in
  undef env l a ty;
  prov env eg l (Ovastart l) [a]

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
    call env eg l x f args vargs
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

(* Try to preserve the last memory access from the parent
   block, which should enable some inter-block redundant
   load elimination.

   If it doesn't exist, then fall back to the solution from
   our last stores analysis.
*)
let setmem env eg l m = env.mem <- match m with
    | None -> Solution.get eg.input.lst l
    | Some _ -> m

let step env eg l lst = match Hashtbl.find eg.input.tbl l with
  | None when Label.is_pseudo l -> ()
  | None | Some `insn _ -> raise @@ Missing l
  | Some `blk b ->
    setmem env eg l lst;
    Blk.insns b |> Seq.iter ~f:(fun i ->
        let l = Insn.label i in
        env.cur <- l;
        insn env eg l (Insn.op i));
    ctrl env eg l @@ Blk.ctrl b

let error_prefix = "In Egraph.Builder"

let try_ f = try Ok (f ()) with
  | Missing l ->
    E.failf "%s: Missing block %a"
      error_prefix Label.pp l ()
  | Duplicate (x, l) ->
    E.failf "%s: duplicate definition of var %a at instruction %a"
      error_prefix Var.pp x Label.pp l ()
  | Rewrite.Type_error (Some a, Some b) ->
    E.failf "%s: type mismatch on rewrite (expected %a, got %a)"
      error_prefix Type.pp a Type.pp b ()
  | Rewrite.Type_error (None, Some b) ->
    E.failf "%s: type mismatch on rewrite (expected nothing, got %a)"
      error_prefix Type.pp b ()
  | Rewrite.Type_error (Some a, None) ->
    E.failf "%s: type mismatch on rewrite (expected %a, got nothing)"
      error_prefix Type.pp a ()
  | Rewrite.Type_error (None, None) ->
    assert false (* impossible *)

let run eg = try_ @@ fun () ->
  let env = init () in
  let q = Stack.singleton (Label.pseudoentry, env.mem) in
  Stack.until_empty q @@ fun (l, lst) ->
  step env eg l lst;
  Tree.children eg.input.dom l |>
  Seq.iter ~f:(fun l -> Stack.push q (l, env.mem))
