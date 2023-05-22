open Core
open Monads.Std
open Regular.Std
open Virtual

module Bitvec = struct
  include Bitvec
  include Bitvec_binprot
  include Bitvec_order
  include Bitvec_sexp
end

module E = Monad.Result.Error

open E.Let

type pure =
  | Palloc  of Label.t * int
  | Pbinop  of Label.t * Insn.binop * pure * pure
  | Pcall   of Label.t * Type.basic * global * pure list * pure list
  | Pdouble of float
  | Pint    of Bitvec.t * Type.imm
  | Pload   of Label.t * Type.basic * pure
  | Psel    of Label.t * Type.basic * pure * pure * pure
  | Psingle of Float32.t
  | Psym    of string * int
  | Punop   of Label.t * Insn.unop * pure
  | Pvar    of Var.t
[@@deriving bin_io, compare, equal, sexp]

and global =
  | Gaddr of Bitvec.t
  | Gpure of pure
  | Gsym  of string
[@@deriving bin_io, compare, equal, sexp]

and local = Label.t * pure list
[@@deriving bin_io, compare, equal, sexp]

and dst =
  | Dglobal of global
  | Dlocal  of local
[@@deriving bin_io, compare, equal, sexp]

type table = (Bitvec.t * local) list
[@@deriving bin_io, compare, equal, sexp]

type t =
  | Ebr      of pure * dst * dst
  | Ecall    of global * pure list * pure list
  | Ehlt
  | Ejmp     of dst
  | Eret     of pure option
  | Eset     of Var.t * pure
  | Estore   of Type.basic * pure * pure
  | Esw      of Type.imm * pure * local * table
  | Evaarg   of Var.t * Type.basic * Var.t
  | Evastart of Var.t
[@@deriving bin_io, compare, equal, sexp]

type ctx = {
  insns  : (insn * blk) Label.Map.t;
  blks   : blk Label.Map.t;
  cfg    : Cfg.t;
  pure   : pure Var.Table.t;
  exp    : t Label.Table.t;
  filled : Var.Hash_set.t;
}

let build_insns fn =
  let init = Label.Map.empty in
  Func.blks fn |> E.Seq.fold ~init ~f:(fun init blk ->
      Blk.insns blk |> E.Seq.fold ~init ~f:(fun m i ->
          let key = Insn.label i in
          match Map.add m ~key ~data:(i, blk) with
          | `Ok m -> Ok m
          | `Duplicate ->
            E.failf "Duplicate label for instruction %a in block %a"
              Label.pp key Label.pp (Blk.label blk) ()))

let create_ctx fn =
  let+ insns = build_insns fn in
  let blks = Func.map_of_blks fn in
  let cfg = Cfg.create fn in
  let pure = Var.Table.create () in
  let exp = Label.Table.create () in
  let filled = Var.Hash_set.create () in
  {insns; blks; cfg; pure; exp; filled}

let rec free_vars_of_pure = function
  | Palloc _ | Pdouble _ | Pint _ | Psingle _ | Psym _ ->
    Var.Set.empty
  | Pbinop (_, _, a, b) ->
    Set.union (free_vars_of_pure a) (free_vars_of_pure b)
  | Pcall (_, _, f, args, vargs) ->
    let args = List.map args ~f:free_vars_of_pure in
    let vargs = List.map vargs ~f:free_vars_of_pure in
    Var.Set.union_list (free_vars_of_global f :: (args @ vargs))
  | Pload (_, _, a) | Punop (_, _, a) -> free_vars_of_pure a
  | Psel (_, _, c, t, f) ->
    Var.Set.union_list [
      free_vars_of_pure c;
      free_vars_of_pure t;
      free_vars_of_pure f;
    ]
  | Pvar v -> Var.Set.singleton v

and free_vars_of_global = function
  | Gaddr _ | Gsym _ -> Var.Set.empty
  | Gpure p -> free_vars_of_pure p

let free_vars_of_local (_, args) =
  List.map args ~f:free_vars_of_pure |> Var.Set.union_list

let free_vars_of_dst = function
  | Dglobal g -> free_vars_of_global g
  | Dlocal l -> free_vars_of_local l

let free_vars_of_table tbl =
  List.map tbl ~f:(fun (_, l) -> free_vars_of_local l) |>
  Var.Set.union_list

let free_vars = function
  | Ebr (c, t, f) ->
    Var.Set.union_list [
      free_vars_of_pure c;
      free_vars_of_dst t;
      free_vars_of_dst f;
    ]
  | Ecall (f, args, vargs) ->
    let args = List.map args ~f:free_vars_of_pure in
    let vargs = List.map vargs ~f:free_vars_of_pure in
    Var.Set.union_list (free_vars_of_global f :: (args @ vargs))
  | Ehlt | Eret None -> Var.Set.empty
  | Ejmp d -> free_vars_of_dst d
  | Eret (Some p) | Eset (_, p) -> free_vars_of_pure p
  | Estore (_, v, a) ->
    Set.union (free_vars_of_pure v) (free_vars_of_pure a)
  | Esw (_, i, d, tbl) ->
    Var.Set.union_list [
      free_vars_of_pure i;
      free_vars_of_local d;
      free_vars_of_table tbl;
    ]
  | Evaarg (_, _, v) | Evastart v ->
    Var.Set.singleton v

let rec labels_of_pure = function
  | Palloc (l, _) -> Label.Set.singleton l
  | Pbinop (l, _, a, b) ->
    let a = labels_of_pure a in
    let b = labels_of_pure b in
    Set.(add (union a b) l)
  | Pcall (l, _, f, args, vargs) ->
    let f = labels_of_global f in
    let args = List.map args ~f:labels_of_pure in
    let vargs = List.map vargs ~f:labels_of_pure in
    Label.Set.(add (union_list (f :: (args @ vargs))) l)
  | Pdouble _ | Pint _ | Psingle _ | Psym _ | Pvar _ -> Label.Set.empty
  | Pload (l, _, a) -> Set.(add (labels_of_pure a) l)
  | Psel (l, _, c, t, f) ->
    let c = labels_of_pure c in
    let t = labels_of_pure t in
    let f = labels_of_pure f in
    Label.Set.(add (union_list [c; t; f]) l)
  | Punop (l, _, a) -> Set.(add (labels_of_pure a) l)

and labels_of_global = function
  | Gaddr _ | Gsym _ -> Label.Set.empty
  | Gpure p -> labels_of_pure p

let labels_of_local (_, args) =
  List.map args ~f:labels_of_pure |>
  Label.Set.union_list

let labels_of_dst = function
  | Dglobal g -> labels_of_global g
  | Dlocal l -> labels_of_local l

let labels_of_table tbl =
  List.map tbl ~f:(fun (_, l) -> labels_of_local l) |>
  Label.Set.union_list

let labels = function
  | Ebr (c, t, f) ->
    Label.Set.union_list [
      labels_of_pure c;
      labels_of_dst t;
      labels_of_dst f;
    ]
  | Ecall (f, args, vargs) ->
    let f = labels_of_global f in
    let args = List.map args ~f:labels_of_pure in
    let vargs = List.map vargs ~f:labels_of_pure in
    Label.Set.union_list (f :: (args @ vargs))
  | Ehlt | Eret None | Evaarg _ | Evastart _ -> Label.Set.empty
  | Ejmp d -> labels_of_dst d
  | Eret (Some p) | Eset (_, p) -> labels_of_pure p
  | Estore (_, v, a) ->
    Set.union (labels_of_pure v) (labels_of_pure a)
  | Esw (_, i, d, tbl) ->
    Label.Set.union_list [
      labels_of_pure i;
      labels_of_local d;
      labels_of_table tbl;
    ]

let is_atom = function
  | Palloc _
  | Pdouble _
  | Pint _
  | Psingle _
  | Psym _
  | Pvar _ -> true
  | _ -> false

exception Occurs_failed of Var.t * Label.t option

let rec subst_pure ?(vs = Var.Set.empty) ctx e =
  let go = subst_pure ctx ~vs in
  match e with
  | Palloc _ as a -> a
  | Pbinop (l, o, x, y) ->
    Pbinop (l, o, go x, go y)
  | Pcall (l, t, f, args, vargs) ->
    let args = List.map args ~f:go in
    let vargs = List.map vargs ~f:go in
    Pcall (l, t, subst_global ctx f ~vs, args, vargs)
  | Pdouble _ as d -> d
  | Pint _ as i -> i
  | Pload (l, t, a) -> Pload (l, t, go a)
  | Psel (l, t, c, y, n) -> Psel (l, t, go c, go y, go n)
  | Psingle _ as s -> s
  | Psym _ as s -> s
  | Punop (l, o, x) -> Punop (l, o, go x)
  | Pvar x when Set.mem vs x -> raise @@ Occurs_failed (x, None)
  | Pvar x as default ->
    Hashtbl.find ctx.pure x |>
    Option.value_map ~default ~f:(continue x vs ctx)

(* Make the full substitution on subterms and cache the results. *)
and continue x vs ctx e =
  if not (is_atom e || Hash_set.mem ctx.filled x) then
    let e = subst_pure ctx e ~vs:(Set.add vs x) in
    Hash_set.add ctx.filled x;
    Hashtbl.set ctx.pure ~key:x ~data:e;
    e
  else e

and subst_global ?(vs = Var.Set.empty) ctx = function
  | (Gaddr _ | Gsym _) as g -> g
  | Gpure p -> Gpure (subst_pure ctx p ~vs)

let subst_local ctx (l, args) = l, List.map args ~f:(subst_pure ctx)

let subst_dst ctx = function
  | Dglobal g -> Dglobal (subst_global ctx g)
  | Dlocal l -> Dlocal (subst_local ctx l)

let rec pp_args args =
  let pp_sep ppf () = Format.fprintf ppf ", " in
  (Format.pp_print_list ~pp_sep pp_pure) args

and pp_pure ppf = function
  | Palloc (l, n) ->
    Format.fprintf ppf "alloc%a(%d)" Label.pp l n
  | Pbinop (l, o, x, y) ->
    Format.fprintf ppf "%a%a(%a, %a)"
      Insn.pp_binop o Label.pp l pp_pure x pp_pure y
  | Pcall (l, _t, f, [], []) ->
    Format.fprintf ppf "%a%a()" pp_global f Label.pp l
  | Pcall (l, _t, f, args, []) ->
    Format.fprintf ppf "%a%a(%a)"
      pp_global f Label.pp l pp_args args
  | Pcall (l, _t, f, [], vargs) ->
    Format.fprintf ppf "%a%a(..., %a)"
      pp_global f Label.pp l pp_args vargs
  | Pcall (l, _t, f, args, vargs) ->
    Format.fprintf ppf "%a%a(%a, ..., %a)"
      pp_global f Label.pp l pp_args args pp_args vargs
  | Pdouble d ->
    Format.fprintf ppf "%a_d" Float.pp d
  | Pint (i, t) ->
    Format.fprintf ppf "%a_%a" Bitvec.pp i Type.pp_imm t
  | Pload (l, t, a) ->
    Format.fprintf ppf "ld.%a%a(%a)"
      Type.pp_basic t Label.pp l pp_pure a
  | Psel (l, t, c, y, n) ->
    Format.fprintf ppf "sel.%a%a(%a, %a, %a)"
      Type.pp_basic t Label.pp l pp_pure c pp_pure y pp_pure n
  | Psingle s ->
    Format.fprintf ppf "%s_s" @@ Float32.to_string s
  | Psym (s, o) ->
    if o = 0 then Format.fprintf ppf "$%s" s
    else if o < 0 then Format.fprintf ppf "$%s-%d" s (lnot o + 1) 
    else Format.fprintf ppf "$%s+%d" s o
  | Punop (l, o, x) ->
    Format.fprintf ppf "%a%a(%a)"
      Insn.pp_unop o Label.pp l pp_pure x
  | Pvar v ->
    Format.fprintf ppf "%a" Var.pp v

and pp_global ppf = function
  | Gaddr a ->
    Format.fprintf ppf "%a" Bitvec.pp a
  | Gpure p ->
    Format.fprintf ppf "%a" pp_pure p
  | Gsym s ->
    Format.fprintf ppf "$%s" s

let pp_local ppf = function
  | l, [] ->
    Format.fprintf ppf "%a" Label.pp l
  | l, args ->
    Format.fprintf ppf "%a(%a)" Label.pp l pp_args args

let pp_dst ppf = function
  | Dglobal g ->
    Format.fprintf ppf "%a" pp_global g
  | Dlocal l ->
    Format.fprintf ppf "%a" pp_local l

let subst_table m = List.map ~f:(fun (i, l) -> i, subst_local m l)

let pp_table tbl =
  let pp_sep ppf () = Format.fprintf ppf "," in
  let pp ppf (v, l) = Format.fprintf ppf "%a:%a" Bitvec.pp v pp_local l in
  (Format.pp_print_list ~pp_sep pp) tbl

let subst ctx e =
  let pure = subst_pure ctx in
  let dst = subst_dst ctx in
  match e with
  | Ebr (c, y, n) -> Ebr (pure c, dst y, dst n)
  | Ecall (f, args, vargs) ->
    let args = List.map args ~f:pure in
    let vargs = List.map vargs ~f:pure in
    Ecall (subst_global ctx f, args, vargs)
  | Ejmp d -> Ejmp (subst_dst ctx d)
  | Eret None as r -> r
  | Eret (Some p) -> Eret (Some (subst_pure ctx p))
  | Eset (x, y) -> Eset (x, subst_pure ctx y ~vs:(Var.Set.singleton x))
  | Estore (t, v, a) -> Estore (t, pure v, pure a)
  | Esw (t, v, d, tbl) ->
    Esw (t, pure v, subst_local ctx d, subst_table ctx tbl)
  | (Ehlt | Evaarg _ | Evastart _) as e -> e

let pp ppf = function
  | Ebr (c, t, f) ->
    Format.fprintf ppf "br(%a, %a, %a)"
      pp_pure c pp_dst t pp_dst f
  | Ecall (f, [], []) ->
    Format.fprintf ppf "%a()" pp_global f
  | Ecall (f, args, []) ->
    Format.fprintf ppf "%a(%a)" pp_global f pp_args args
  | Ecall (f, [], vargs) ->
    Format.fprintf ppf "%a(..., %a)" pp_global f pp_args vargs
  | Ecall (f, args, vargs) ->
    Format.fprintf ppf "%a(%a, ..., %a)"
      pp_global f pp_args args pp_args vargs
  | Ehlt ->
    Format.fprintf ppf "hlt"
  | Ejmp d ->
    Format.fprintf ppf "jmp(%a)" pp_dst d
  | Eret (Some x) ->
    Format.fprintf ppf "ret(%a)" pp_pure x
  | Eret None ->
    Format.fprintf ppf "ret"
  | Eset (x, y) ->
    Format.fprintf ppf "%a = %a" Var.pp x pp_pure y
  | Estore (t, v, a) ->
    Format.fprintf ppf "st%a(%a, %a)"
      Type.pp_basic t pp_pure v pp_pure a
  | Esw (t, v, d, tbl) ->
    Format.fprintf ppf "sw.%a(%a, %a, [%a])"
      Type.pp_imm t pp_pure v pp_local d pp_table tbl
  | Evaarg (x, t, y) ->
    Format.fprintf ppf "%a = vaarg.%a(%a)"
      Var.pp x Type.pp_basic t Var.pp y
  | Evastart x ->
    Format.fprintf ppf "vastart(%a)" Var.pp x

let operand (o : operand) w = match o with
  | `int (i, t) -> Pint (i, t), w
  | `float f    -> Psingle f, w
  | `double d   -> Pdouble d, w
  | `sym (s, o) -> Psym (s, o), w
  | `var v      -> Pvar v, Set.add w v

let operands os w =
  List.fold_right os ~init:([], w) ~f:(fun o (os, w) ->
      let o, w = operand o w in
      o :: os, w)

let global (g : Virtual.global) w = match g with
  | `addr a -> Gaddr a, w
  | `sym s  -> Gsym s, w
  | `var v  -> Gpure (Pvar v), Set.add w v

let local (l : Virtual.local) w = match l with
  | `label (l, args) ->
    let args, w = operands args w in
    (l, args), w

let dst (d : Virtual.dst) w = match d with
  | #Virtual.global as g ->
    let g, w = global g w in
    Dglobal g, w
  | #Virtual.local as l ->
    let l, w = local l w in
    Dlocal l, w

(* We assume that the function is in SSA form, which should enforce
   the invariant that all variables are bound to the same expression. *)
let accum ctx w l x f =
  if Set.mem w x then
    let w = Set.remove w x in
    if not @@ Hashtbl.mem ctx.pure x then
      let w, p = f w in
      if Set.mem w x then raise @@ Occurs_failed (x, Some l);
      Hashtbl.set ctx.pure ~key:x ~data:p;
      w
    else w
  else w

(* Accumulate the results of an instruction. *)
let insn ctx w i =
  let l = Insn.label i in
  let go = accum ctx w l in
  match Insn.op i with
  | `bop (x, o, a, b) -> go x @@ fun w ->
    let a, w = operand a w in
    let b, w = operand b w in
    w, Pbinop (l, o, a, b)
  | `uop (x, o, a) -> go x @@ fun w ->
    let a, w = operand a w in
    w, Punop (l, o, a)
  | `sel (x, t, c, y, n) -> go x @@ fun w ->
    let c, w = Pvar c, Set.add w c in
    let y, w = operand y w in
    let n, w = operand n w in
    w, Psel (l, t, c, y, n)
  | `call (Some (x, t), f, args, vargs) -> go x @@ fun w ->
    let f, w = global f w in
    let args, w = operands args w in
    let vargs, w = operands vargs w in
    w, Pcall (l, t, f, args, vargs)
  | `alloc (x, n) -> go x @@ fun w -> w, Palloc (l, n)
  | `load (x, t, a) -> go x @@ fun w ->
    let a, w = operand a w in
    w, Pload (l, t, a)
  | _ -> w

(* Kill the variables that appear in the arguments of the block.
   This is the point where we can no longer represent their data
   dependencies as a DAG. *)
let killed blk w =
  Blk.args blk |> Seq.map ~f:fst |> Var.Set.of_sequence |> Set.diff w

(* Get the subset of instructions that we need to inspect backwards
   and then accumulate the results. *)
let insns ?l ctx blk w =
  Blk.insns blk ~rev:true |> fun ss ->
  Option.value_map l ~default:ss ~f:(fun l ->
      Seq.drop_while_option ss ~f:(fun i ->
          Label.(l <> Insn.label i)) |>
      Option.value_map ~default:Seq.empty ~f:snd) |>
  Seq.fold ~init:w ~f:(insn ctx) |> killed blk

(* Next blocks to visit. *)
let nexts ctx blk bs =
  Cfg.Node.preds (Blk.label blk) ctx.cfg |>
  Seq.filter_map ~f:(fun l ->
      if Label.is_pseudo l || Set.mem bs l
      then None else Map.find ctx.blks l)

(* Traverse the data dependencies. *)
let build ?(w = Var.Set.empty) ?l ctx blk =
  let q = Stack.singleton (blk, w, Label.Set.empty) in
  while not @@ Stack.is_empty q do
    let blk, w, bs = Stack.pop_exn q in
    let w = insns ?l ctx blk w in
    if not @@ Set.is_empty w then
      let bs = Set.add bs @@ Blk.label blk in
      nexts ctx blk bs |> Seq.iter ~f:(fun blk ->
          Stack.push q (blk, w, bs))
  done

let table tbl w =
  Ctrl.Table.enum tbl |>
  Seq.fold ~init:([], w) ~f:(fun (tbl, w) (i, l) ->
      let l, w = local l w in
      (i, l) :: tbl, w) |> fun (tbl, w) ->
  List.rev tbl, w

let go_ctrl ctx blk f =
  let w, e = f () in
  build ctx blk ~w;
  let e = subst ctx e in
  Hashtbl.set ctx.exp ~key:(Blk.label blk) ~data:e;
  e

let of_ctrl ctx blk =
  let go = go_ctrl ctx blk in
  match Blk.ctrl blk with
  | `hlt -> Ehlt
  | `jmp d -> go @@ fun () ->
    let d, w = dst d Var.Set.empty in
    w, Ejmp d
  | `br (c, y, n) -> go @@ fun () ->
    let c, w = Pvar c, Var.Set.singleton c in
    let y, w = dst y w in
    let n, w = dst n w in
    w, Ebr (c, y, n)
  | `ret None -> Eret None
  | `ret (Some x) -> go @@ fun () ->
    let x, w = operand x Var.Set.empty in
    w, Eret (Some x)
  | `sw (t, v, d, tbl) -> go @@ fun () ->
    let v, w = Pvar v, Var.Set.singleton v in
    let d, w = local d w in
    let tbl, w = table tbl w in
    w, Esw (t, v, d, tbl)

let go_insn ctx blk l f =
  let w, e = f () in
  build ctx blk ~l ~w;
  let e = subst ctx e in
  Hashtbl.set ctx.exp ~key:l ~data:e;
  e

let of_insn ctx i blk =
  let l = Insn.label i in
  let go = go_insn ctx blk l in
  match Insn.op i with
  | `bop (x, o, a, b) -> go @@ fun () ->
    let a, w = operand a Var.Set.empty in
    let b, w = operand b w in
    w, Eset (x, Pbinop (l, o, a, b))
  | `uop (x, o, a) -> go @@ fun () ->
    let a, w = operand a Var.Set.empty in
    w, Eset (x, Punop (l, o, a))
  | `sel (x, t, c, y, n) -> go @@ fun () ->
    let y, w = operand y @@ Var.Set.singleton c in
    let n, w = operand n w in
    w, Eset (x, Psel (l, t, Pvar c, y, n))
  | `call (Some (x, t), f, args, vargs) -> go @@ fun () ->
    let f, w = global f Var.Set.empty in
    let args, w = operands args w in
    let vargs, w = operands vargs w in
    w, Eset (x, Pcall (l, t, f, args, vargs))
  | `alloc (x, n) -> go @@ fun () ->
    Var.Set.empty, Eset (x, Palloc (l, n))
  | `load (x, t, a) -> go @@ fun () ->
    let a, w = operand a Var.Set.empty in
    w, Eset (x, Pload (l, t, a))
  | `call (None, f, args, vargs) -> go @@ fun () ->
    let f, w = global f Var.Set.empty in
    let args, w = operands args w in
    let vargs, w = operands vargs w in
    w, Ecall (f, args, vargs)
  | `store (t, v, a) -> go @@ fun () ->
    let v, w = operand v Var.Set.empty in
    let a, w = operand a w in
    w, Estore (t, v, a)
  | `vaarg (x, t, y) -> Evaarg (x, t, y)
  | `vastart x -> Evastart x

let build ctx l = try match Hashtbl.find ctx.exp l with
  | Some e -> Ok e
  | None -> match Map.find ctx.blks l with
    | Some blk -> Ok (of_ctrl ctx blk)
    | None -> match Map.find ctx.insns l with
      | Some (i, blk) -> Ok (of_insn ctx i blk)
      | None -> E.failf "Label %a not found" Label.pp l ()
  with
  | Occurs_failed (x, None) ->
    E.failf "Occurs check failed for variable %a" Var.pp x ()
  | Occurs_failed (x, Some l) ->
    E.failf "Occurs check failed for variable %a at instruction %a"
      Var.pp x Label.pp l ()
