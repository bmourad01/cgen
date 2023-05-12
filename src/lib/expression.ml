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

let rec subst_pure m = function
  | Palloc _ as a -> a
  | Pbinop (l, o, x, y) ->
    Pbinop (l, o, subst_pure m x, subst_pure m y)
  | Pcall (l, t, f, args, vargs) ->
    let args = List.map args ~f:(subst_pure m) in
    let vargs = List.map vargs ~f:(subst_pure m) in
    Pcall (l, t, subst_global m f, args, vargs)
  | Pdouble _ as d -> d
  | Pint _ as i -> i
  | Pload (l, t, a) -> Pload (l, t, subst_pure m a)
  | Psel (l, t, c, y, n) ->
    Psel (l, t, subst_pure m c, subst_pure m y, subst_pure m n)
  | Psingle _ as s -> s
  | Psym _ as s -> s
  | Punop (l, o, x) -> Punop (l, o, subst_pure m x)
  | Pvar x as default ->
    Map.find m x |> Option.value ~default

and subst_global m = function
  | (Gaddr _ | Gsym _) as g -> g
  | Gpure p -> Gpure (subst_pure m p)

let subst_local m (l, args) = l, List.map args ~f:(subst_pure m)

let subst_dst m = function
  | Dglobal g -> Dglobal (subst_global m g)
  | Dlocal l -> Dlocal (subst_local m l)

let rec pp_args args =
  let pp_sep ppf () = Format.fprintf ppf "," in
  (Format.pp_print_list ~pp_sep pp_pure) args

and pp_pure ppf = function
  | Palloc (l, n) ->
    Format.fprintf ppf "alloc%a(%d)" Label.pp l n
  | Pbinop (l, o, x, y) ->
    Format.fprintf ppf "%a%a(%a,%a)"
      Label.pp l Insn.pp_binop o pp_pure x pp_pure y
  | Pcall (l, _t, f, [], []) ->
    Format.fprintf ppf "%a%a()" Label.pp l pp_global f
  | Pcall (l, _t, f, args, []) ->
    Format.fprintf ppf "%a%a(%a)"
      Label.pp l pp_global f pp_args args
  | Pcall (l, _t, f, [], vargs) ->
    Format.fprintf ppf "%a%a(...,%a)"
      Label.pp l pp_global f pp_args vargs
  | Pcall (l, _t, f, args, vargs) ->
    Format.fprintf ppf "%a%a(%a,...,%a)"
      Label.pp l pp_global f pp_args args pp_args vargs
  | Pdouble d ->
    Format.fprintf ppf "%a_d" Float.pp d
  | Pint (i, t) ->
    Format.fprintf ppf "%a_%a" Bitvec.pp i Type.pp_imm t
  | Pload (l, t, a) ->
    Format.fprintf ppf "ld.%a%a(%a)"
      Label.pp l Type.pp_basic t pp_pure a
  | Psel (l, t, c, y, n) ->
    Format.fprintf ppf "sel.%a%a(%a,%a,%a)"
      Type.pp_basic t Label.pp l pp_pure c pp_pure y pp_pure n
  | Psingle s ->
    Format.fprintf ppf "%s_s" @@ Float32.to_string s
  | Psym (s, o) ->
    if o = 0 then Format.fprintf ppf "$%s" s
    else if o < 0 then Format.fprintf ppf "$%s-%d" s (lnot o + 1) 
    else Format.fprintf ppf "$%s+%d" s o
  | Punop (l, o, x) ->
    Format.fprintf ppf "%a%a(%a)"
      Label.pp l Insn.pp_unop o pp_pure x
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

type table = (Bitvec.t * local) list
[@@deriving bin_io, compare, equal, sexp]

let subst_table m = List.map ~f:(fun (i, l) -> i, subst_local m l)

let pp_table tbl =
  let pp_sep ppf () = Format.fprintf ppf "," in
  let pp ppf (v, l) = Format.fprintf ppf "%a:%a" Bitvec.pp v pp_local l in
  (Format.pp_print_list ~pp_sep pp) tbl

type t =
  | Ebr    of pure * dst * dst
  | Ecall  of global * pure list * pure list
  | Ejmp   of dst
  | Eret   of pure
  | Eset   of Var.t * pure
  | Estore of Type.basic * pure * pure
  | Esw    of Type.imm * pure * local * table
[@@deriving bin_io, compare, equal, sexp]

let subst m = function
  | Ebr (c, y, n) ->
    Ebr (subst_pure m c, subst_dst m y, subst_dst m n)
  | Ecall (f, args, vargs) ->
    let args = List.map args ~f:(subst_pure m) in
    let vargs = List.map vargs ~f:(subst_pure m) in
    Ecall (subst_global m f, args, vargs)
  | Ejmp d -> Ejmp (subst_dst m d)
  | Eret r -> Eret (subst_pure m r)
  | Eset (x, y) -> Eset (x, subst_pure m y)
  | Estore (t, v, a) ->
    Estore (t, subst_pure m v, subst_pure m a)
  | Esw (t, v, d, tbl) ->
    Esw (t, subst_pure m v, subst_local m d, subst_table m tbl)

let pp ppf = function
  | Ebr (c, t, f) ->
    Format.fprintf ppf "br(%a,%a,%a)"
      pp_pure c pp_dst t pp_dst f
  | Ecall (f, [], []) ->
    Format.fprintf ppf "%a()" pp_global f
  | Ecall (f, args, []) ->
    Format.fprintf ppf "%a(%a)" pp_global f pp_args args
  | Ecall (f, [], vargs) ->
    Format.fprintf ppf "%a(...,%a)" pp_global f pp_args vargs
  | Ecall (f, args, vargs) ->
    Format.fprintf ppf "%a(%a,...,%a)"
      pp_global f pp_args args pp_args vargs
  | Ejmp d ->
    Format.fprintf ppf "jmp(%a)" pp_dst d
  | Eret x ->
    Format.fprintf ppf "ret(%a)" pp_pure x
  | Eset (x, y) ->
    Format.fprintf ppf "%a = %a" Var.pp x pp_pure y
  | Estore (t, v, a) ->
    Format.fprintf ppf "st%a(%a,%a)"
      Type.pp_basic t pp_pure v pp_pure a
  | Esw (t, v, d, tbl) ->
    Format.fprintf ppf "sw.%a(%a,%a,[%a])"
      Type.pp_imm t pp_pure v pp_local d pp_table tbl

module E = Monad.Result.Error

open E.Let
open E.Syntax

type env = {
  blks : blk Label.Map.t;
  cfg  : Cfg.t;
  seen : Label.Hash_set.t;
}

let create_env fn =
  let blks = Func.map_of_blks fn in
  {blks; cfg = Cfg.create fn; seen = Label.Hash_set.create ()}

let operand (o : operand) w = match o with
  | `int (i, t) -> Pint (i, t), w
  | `float f -> Psingle f, w
  | `double d -> Pdouble d, w
  | `sym (s, o) -> Psym (s, o), w
  | `var v -> Pvar v, Set.add w v

let operands os w = List.fold_right os ~init:([], w) ~f:(fun o (os, w) ->
    let o, w = operand o w in
    o :: os, w)

let global (g : Virtual.global) w = match g with
  | `addr a -> Gaddr a, w
  | `sym s -> Gsym s, w
  | `var v -> Gpure (Pvar v), Set.add w v

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

let assign w vs x e = match Map.add vs ~key:x ~data:e with
  | `Duplicate -> E.failf "Duplicate assignment to var %a" Var.pp x ()
  | `Ok vs -> !!(Set.remove w x, vs)

let rec build ?(w = Var.Set.empty) ?(vs = Var.Map.empty) ?l env blk =
  Hash_set.add env.seen @@ Blk.label blk;
  Blk.insns blk ~rev:true |> fun ss ->
  Option.value_map l ~default:ss ~f:(fun l ->
      Seq.drop_while ss ~f:(fun i -> Label.(l <> Insn.label i)) |>
      Fn.flip Seq.drop 1) |>
  E.Seq.fold ~init:(w, vs) ~f:(fun (w, vs) i ->
      let l = Insn.label i in
      match Insn.op i with
      | `bop (x, o, a, b) when Set.mem w x ->
        let a, w = operand a w in
        let b, w = operand b w in
        assign w vs x @@ Pbinop (l, o, a, b)
      | `uop (x, o, a) when Set.mem w x ->
        let a, w = operand a w in
        assign w vs x @@ Punop (l, o, a)
      | `sel (x, t, c, y, n) when Set.mem w x ->
        let c, w = Pvar c, Set.add w c in
        let y, w = operand y w in
        let n, w = operand n w in
        assign w vs x @@ Psel (l, t, c, y, n)
      | `call (Some (x, t), f, args, vargs) when Set.mem w x ->
        let f, w = global f w in
        let args, w = operands args w in
        let vargs, w = operands vargs w in
        assign w vs x @@ Pcall (l, t, f, args, vargs)
      | `alloc (x, n) when Set.mem w x ->
        assign w vs x @@ Palloc (l, n)
      | `load (x, t, a) when Set.mem w x ->
        let a, w = operand a w in
        assign w vs x @@ Pload (l, t, a)
      | _ -> Ok (w, vs)) >>= fun (w, vs) ->
  let w =
    Set.diff w @@
    Var.Set.of_sequence @@
    Seq.map ~f:fst @@ Blk.args blk in
  if not @@ Set.is_empty w then
    Cfg.Node.preds (Blk.label blk) env.cfg |>
    Seq.filter ~f:(fun l ->
        not (Label.is_pseudo l || Hash_set.mem env.seen l)) |>
    E.Seq.fold ~init:vs ~f:(fun vs l ->
        let blk = Map.find_exn env.blks l in
        build env blk ~w ~vs)
  else !!vs

let of_ctrl env blk = match Blk.ctrl blk with
  | `hlt -> !!None
  | `jmp d ->
    let d, w = dst d Var.Set.empty in
    let+ vs = build env blk ~w in
    Some (subst vs @@ Ejmp d)
  | `br (c, y, n) ->
    let c, w = Pvar c, Var.Set.singleton c in
    let y, w = dst y w in
    let n, w = dst n w in
    let+ vs = build env blk ~w in
    Some (subst vs @@ Ebr (c, y, n))
  | `ret None -> !!None
  | `ret (Some x) ->
    let x, w = operand x Var.Set.empty in
    let+ vs = build env blk ~w in
    Some (subst vs @@ Eret x)
  | `sw (t, v, d, tbl) ->
    let v, w = Pvar v, Var.Set.singleton v in
    let d, w = local d w in
    let tbl, w =
      Ctrl.Table.enum tbl |>
      Seq.fold ~init:([], w) ~f:(fun (tbl, w) (i, l) ->
          let l, w = local l w in
          (i, l) :: tbl, w) in
    let+ vs = build env blk ~w in
    Some (subst vs @@ Esw (t, v, d, List.rev tbl))

let of_insn env i blk =
  let op = Insn.op i in
  let l = Insn.label i in
  match op with
  | `bop (x, _, _, _)
  | `uop (x, _, _)
  | `sel (x, _, _, _, _)
  | `call (Some (x, _), _, _, _)
  | `alloc (x, _)
  | `load (x, _, _) ->
    let+ vs = build env blk ~w:(Var.Set.singleton x) in
    Some (subst vs @@ Eset (x, Map.find_exn vs x))
  | `call (None, f, args, vargs) ->
    let f, w = global f Var.Set.empty in
    let args, w = operands args w in
    let vargs, w = operands vargs w in
    let+ vs = build env blk ~l ~w in
    Some (subst vs @@ Ecall (f, args, vargs))
  | `store (t, v, a) ->
    let v, w = operand v Var.Set.empty in
    let a, w = operand a w in
    let+ vs = build env blk ~l ~w in
    Some (subst vs @@ Estore (t, v, a))
  | `vastart _ | `vaarg _ -> !!None

let find_insn fn l =
  Func.blks fn |> Seq.find_map ~f:(fun blk ->
      Blk.insns blk |> Seq.find_map ~f:(fun i ->
          if Label.(l <> Insn.label i) then None else Some (i, blk)))

let build fn l =
  let env = create_env fn in
  match Map.find env.blks l with
  | Some blk -> of_ctrl env blk
  | None -> match find_insn fn l with
    | Some (insn, blk) -> of_insn env insn blk
    | None ->
      E.failf "Label %a not found in function $%s"
        Label.pp l (Func.name fn) ()
