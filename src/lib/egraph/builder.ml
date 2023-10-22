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
  vars        : id Var.Table.t;
  mems        : st Mem.Table.t;
  mutable cur : Label.t;
  mutable lst : Label.t option;
}

let init () = {
  vars = Var.Table.create ();
  mems = Mem.Table.create ();
  cur = Label.pseudoentry;
  lst = None;
}

let cur_interval env eg x =
  let open Monad.Option.Let in
  let* s = Intervals.insn eg.input.intv env.cur in
  Intervals.find_var s x

let node ?iv ?ty ?l env eg op args =
  Rewrite.insert ?iv ?ty ?l ~d:eg.fuel eg @@ N (op, args)

let atom ?iv ?ty env eg op = node ?iv ?ty env eg op []

let constant ?iv ?ty env eg k =
  Rewrite.insert ?iv ?ty ~d:eg.fuel eg @@ Enode.of_const k

let var env eg x =
  let iv = cur_interval env eg x in
  let ty = typeof_var eg x in
  Hashtbl.find_and_call env.vars x
    ~if_not_found:(fun _ ->
        (* This var is either a block param, a function argument,
           or a stack slot. *)
        match Util.single_interval iv ty with
        | Some k -> constant ?iv ?ty env eg k
        | None -> atom ?iv ?ty env eg @@ Ovar x)
    ~if_found:(fun id ->
        (* This var was defined by an instruction. *)
        match Util.single_interval iv ty with
        | Some k -> constant ?iv ?ty env eg k
        | None ->
          setiv ?iv eg id;
          id)

let typeof_const eg : const -> Type.t = function
  | `bool _ -> `flag
  | `int (_, t) -> (t :> Type.t)
  | `float _ -> `f32
  | `double _ -> `f64
  | `sym _ -> word eg

let operand env eg : operand -> id = function
  | #const as c ->
    let ty = typeof_const eg c in
    let iv = Util.interval_of_const c ~wordsz:(wordsz eg) in
    constant ~iv ~ty env eg c
  | `var x -> var env eg x

let operands env eg = List.map ~f:(operand env eg)

let global env eg : global -> id = function
  | `addr a -> atom ~ty:(word eg) env eg @@ Oaddr a
  | `sym (s, o) -> atom ~ty:(word eg) env eg @@ Osym (s, o)
  | `var x -> var env eg x

let local env eg : local -> id = function
  | `label (l, args) -> node env eg (Olocal l) (operands env eg args)

let dst env eg : dst -> id = function
  | #global as g -> global env eg g
  | #local as l -> local env eg l

let table env eg tbl =
  Ctrl.Table.enum tbl |> Seq.map ~f:(fun (i, l) ->
      node env eg (Otbl i) [local env eg l]) |> Seq.to_list

let prov_interval ?x eg l =
  let open Monad.Option.Let in
  let* x = x in
  let* s = Intervals.insn eg.input.intv l in
  Intervals.find_var s x

let prov ?x ?(f = Fn.const) env eg l op args =
  let ty = Option.bind x ~f:(typeof_var eg) in
  let iv = prov_interval ?x eg l in
  let id = node ?iv ?ty ~l env eg op args in
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
  prov env eg l (Ostore (ty, l)) [v; a];
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

let callop x l : Enode.op * Var.t option = match x with
  | Some (x, t) -> Ocall (x, t), Some x
  | None -> Ocall0 l, None

let callargs env eg args =
  node env eg Ocallargs @@ operands env eg args

(* Our analysis is intraprocedural, so assume that a function call
   can do any arbitrary effects to memory. *)
let call env eg l x f args vargs =
  let op, x = callop x l in
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
  let a = alist env eg a in
  undef env l a ty;
  prov ~x env eg l (Ovaarg (x, ty)) [a]

let vastart env eg l x =
  let a = alist env eg x in
  let tgt = Typecheck.Env.target eg.input.tenv in
  let ty = (Target.word tgt :> Type.basic) in
  undef env l a ty;
  prov env eg l (Ovastart l) [a]

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
  | `tcall (t, f, args, vargs) ->
    let o : Enode.op = match t with
      | Some t -> Otcall t
      | None -> Otcall0 in
    prov env eg l o [
      global env eg f;
      callargs env eg args;
      callargs env eg vargs;
    ]

let step env eg l = match Hashtbl.find eg.input.tbl l with
  | None when Label.is_pseudo l -> ()
  | None | Some `insn _ -> raise @@ Missing l
  | Some `blk b ->
    env.lst <- Solution.get eg.input.lst l;
    Blk.insns b |> Seq.iter ~f:(fun i ->
        let l = Insn.label i in
        env.cur <- l;
        insn env eg l (Insn.op i));
    ctrl env eg l @@ Blk.ctrl b

let try_ f = try Ok (f ()) with
  | Missing l ->
    E.failf "Missing block %a" Label.pp l ()
  | Duplicate (x, l) ->
    E.failf "Duplicate definition of var %a at instruction %a"
      Var.pp x Label.pp l ()

let run eg = try_ @@ fun () ->
  let env = init () in
  let q = Stack.singleton Label.pseudoentry in
  while not @@ Stack.is_empty q do
    let l = Stack.pop_exn q in
    step env eg l;
    Tree.children eg.input.dom l |>
    Seq.iter ~f:(Stack.push q);
  done
