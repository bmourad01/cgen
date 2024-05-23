(* Simplified version of the memory optimizations found in the
   `Egraph` module.

   The simplified portion is the canonicalization of operands via
   hash-consing, since we're not rolling out the heavy artilery
   of the e-graph framework.
*)

open Core
open Monads.Std
open Regular.Std
open Graphlib.Std
open Virtual

module E = Monad.Result.Error

open E.Let

module Op = struct
  type t =
    | Bop of Abi.Insn.binop * operand * operand
    | Uop of Abi.Insn.unop * operand
    | Sel of Type.basic * Var.t * operand * operand
  [@@deriving compare, equal, hash, sexp]

  let commute = function
    | Bop (b, l, r) ->
      begin match b with
        | `add _
        | `mul _
        | `mulh _
        | `umulh _
        | `and_ _
        | `or_ _
        | `xor _
        | `eq _
        | `ne _ -> Some (Bop (b, r, l))
        | _ -> None
      end
    | _ -> None

  let of_insn = function
    | `bop (_, o, a, b) -> Bop (o, a, b)
    | `uop (_, o, a) -> Uop (o, a)
    | `sel (_, ty, c, y, n) -> Sel (ty, c, y, n)
end

module Hashcons = Hashmap.Make(Op)

type mem = {
  label : Label.t;
  addr  : operand;
  ty    : Type.basic;
} [@@deriving bin_io, compare, equal, hash, sexp]

type store =
  | Undef
  | Value of operand * Label.t
[@@deriving sexp]

module Mem = Regular.Make(struct
    type t = mem [@@deriving bin_io, compare, equal, hash, sexp]
    let pp ppf t = Format.fprintf ppf "%a" Sexp.pp_hum @@ sexp_of_t t
    let module_name = Some "Cgen.Passes.Abi_loadopt.Mem"
    let version = "0.1"
  end)

(* Bindings from variables to canonicalized operands. We use a
   persistent map because the bindings are scoped according to
   our traversal of the dominator tree. *)
type scope = operand Var.Map.t

type t = {
  reso         : Abi.resolver;
  dom          : Label.t tree;
  cdom         : Cdoms.t;
  lst          : Last_stores.t;
  blks         : Abi.blk Label.Table.t;
  mems         : store Mem.Table.t;
  mutable mem  : Label.t option;
  mutable memo : operand Hashcons.t;
  mutable vars : scope;
}

let init_cdoms reso dom =
  let module Cdom = Cdoms.Make(struct
      type lhs = Var.Set.t
      type insn = Abi.insn
      module Blk = Abi.Blk
      let rec is_descendant_of ~parent l = match Tree.parent dom l with
        | Some p -> Label.(p = parent) || is_descendant_of ~parent p
        | None -> false
      let resolve = Abi.Resolver.resolve reso
    end) in
  Cdom.dominates

let init_last_stores cfg reso =
  let module Lst = Last_stores.Make(struct
      module Insn = Abi.Insn
      module Blk = Abi.Blk
      module Cfg = Abi.Cfg
      let resolve l = match Abi.Resolver.resolve reso l with
        | Some `insn _ | None -> assert false
        | Some `blk b -> b
    end) in
  Lst.analyze cfg

let init fn =
  let+ reso = Abi.Resolver.create fn in
  let cfg = Abi.Cfg.create fn in
  let dom = Graphlib.dominators (module Abi.Cfg) cfg Label.pseudoentry in
  let cdom = init_cdoms reso dom in
  let lst = init_last_stores cfg reso in
  let blks = Label.Table.create () in
  let mems = Mem.Table.create () in
  let mem = None and memo = Hashcons.empty and vars = Var.Map.empty in
  {reso; dom; cdom; lst; blks; mems; mem; memo; vars}

module Optimize = struct
  let var t x = match Map.find t.vars x with
    | None -> `var x
    | Some y -> y

  let operand t : operand -> operand = function
    | #const as c -> c
    | `var x -> var t x

  let operands t = List.map ~f:(operand t)

  let local t : local -> local = function
    | `label (l, args) -> `label (l, operands t args)

  let global t : global -> global = function
    | (`addr _ | `sym _) as g -> g
    | `var x -> match var t x with
      | (`sym _ | `var _) as y -> y
      | `int (i, _) -> `addr i
      | _ -> assert false

  let dst t : dst -> dst = function
    | #local as l -> (local t l :> dst)
    | #global as g -> (global t g :> dst)

  let table t =
    Abi.Ctrl.Table.map_exn ~f:(fun i l -> i, local t l)

  let callargs t = List.map ~f:(function
      | `reg (o, r) -> `reg (operand t o, r)
      | `stk (o, s) -> `stk (operand t o, s))

  let canonicalize t x op =
    t.memo <- Hashcons.update t.memo op ~f:(function
        | Some y -> t.vars <- Map.set t.vars ~key:x ~data:y; y
        | None -> match op with
          | Uop (`copy _, a) ->
            t.vars <- Map.set t.vars ~key:x ~data:a; a
          | _ -> `var x)

  let store t l ty v a =
    let v = operand t v in
    let a = operand t a in
    let key = {label = l; addr = a; ty} in
    Hashtbl.set t.mems ~key ~data:(Value (v, l));
    t.mem <- Some l;
    `store (ty, v, a)

  let alias t key l =
    Hashtbl.find t.mems key |>
    Option.bind ~f:(function
        | Undef -> None
        | Value (v, parent) ->
          Option.some_if (t.cdom ~parent l) v)

  let load t l x ty a =
    let a = operand t a in
    let mem = match t.mem with
      | None -> t.mem <- Some l; l
      | Some l -> l in
    let key = {label = mem; addr = a; ty} in
    match alias t key l with
    | None -> `load (x, ty, a)
    | Some v ->
      let op = `uop (x, `copy ty, v) in
      canonicalize t x @@ Op.of_insn op;
      op

  let basics = [|`i8; `i16; `i32; `i64; `f32; `f64|]

  let undef t l addr =
    Array.iter basics ~f:(fun ty ->
        Hashtbl.set t.mems ~key:{label = l; addr; ty} ~data:Undef);
    t.mem <- Some l

  let sel t x ty c y n =
    let y = operand t y in
    let n = operand t n in
    let op = match var t c with
      | `bool true -> `uop (x, `copy ty, y)
      | `bool false -> `uop (x, `copy ty, n)
      | `var c -> `sel (x, ty, c, y, n)
      | _ -> assert false in
    canonicalize t x @@ Op.of_insn op;
    op

  let call t l xs f args =
    let f = global t f in
    let args = callargs t args in
    t.mem <- Some l;
    `call (xs, f, args)

  let insn t l : Abi.Insn.op -> Abi.Insn.op = function
    | `bop (x, o, a, b) ->
      let op = `bop (x, o, operand t a, operand t b) in
      let k = Op.of_insn op in
      canonicalize t x k;
      Op.commute k |> Option.iter ~f:(canonicalize t x);
      op
    | `uop (x, o, a) ->
      let op = `uop (x, o, operand t a) in
      canonicalize t x @@ Op.of_insn op;
      op
    | `sel (x, ty, c, y, n) -> sel t x ty c y n
    | `call (xs, f, args) -> call t l xs f args
    | `store (ty, v, a) -> store t l ty v a
    | `load (x, ty, a) -> load t l x ty a
    | `loadreg _ as lr -> lr
    | `storereg (r, a) ->
      let a = operand t a in
      undef t l a;
      `storereg (r, a)
    | `setreg (r, a) -> `setreg (r, operand t a)
    | `stkargs _ as sa -> sa

  let br t c y n =
    let y = dst t y in
    let n = dst t n in
    match var t c with
    | `bool true -> `jmp y
    | `bool false -> `jmp n
    | `var c -> `br (c, y, n)
    | _ -> assert false

  let sw t ty i d tbl =
    let d = local t d in
    let tbl = table t tbl in
    match i with
    | `sym _ -> `sw (ty, i, d, tbl)
    | `var x -> match var t x with
      | (`var _ | `sym _) as y -> `sw (ty, y, d, tbl)
      | `int (i, _) ->
        let d =
          Abi.Ctrl.Table.find tbl i |>
          Option.value ~default:d in
        `jmp (d :> dst)
      | _ -> assert false

  let ctrl t : Abi.ctrl -> Abi.ctrl = function
    | `hlt -> `hlt
    | `jmp d -> `jmp (dst t d)
    | `br (c, y, n) -> br t c y n
    | `ret rs -> `ret (List.map rs ~f:(fun (r, o) -> r, operand t o))
    | `sw (ty, i, d, tbl) -> sw t ty i d tbl

  let setmem t l m = t.mem <- match m with
      | None -> Solution.get t.lst l
      | Some _ -> m

  let step t l lst memo vars = match Abi.Resolver.resolve t.reso l with
    | None when Label.is_pseudo l -> ()
    | None | Some `insn _ -> assert false
    | Some `blk b ->
      setmem t l lst;
      t.memo <- memo;
      t.vars <- vars;
      let b = Abi.Blk.map_insns b ~f:(insn t) in
      let b = Abi.Blk.map_ctrl b ~f:(ctrl t) in
      Hashtbl.set t.blks ~key:l ~data:b
end

let run fn =
  if Dict.mem (Abi.Func.dict fn) Tags.ssa then
    let+ t = init fn in
    let q = Stack.singleton (Label.pseudoentry, t.mem, t.memo, t.vars) in
    Stack.until_empty q (fun (l, lst, memo, vars) ->
        Optimize.step t l lst memo vars;
        Tree.children t.dom l |> Seq.iter ~f:(fun l ->
            Stack.push q (l, t.mem, t.memo, t.vars)));
    Abi.Func.map_blks fn ~f:(fun b ->
        Abi.Blk.label b |> Hashtbl.find t.blks |>
        Option.value ~default:b)
  else
    E.failf "In Abi_loadopt: function $%s is not in SSA form"
      (Abi.Func.name fn) ()
