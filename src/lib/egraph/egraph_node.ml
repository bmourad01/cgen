open Core
open Virtual

module Id = Egraph_id

type op =
  | Oaddr     of Bv.t
  | Obinop    of Insn.binop
  | Obool     of bool
  | Obr
  | Ocall0    of Label.t
  | Ocall     of Var.t * Type.ret
  | Ocallargs
  | Odouble   of float
  | Ojmp
  | Oint      of Bv.t * Type.imm
  | Oload     of Var.t * Type.arg
  | Olocal    of Label.t
  | Oret
  | Osel      of Type.basic
  | Oset      of Var.t
  | Osingle   of Float32.t
  | Ostore    of Type.arg * Label.t
  | Osw       of Type.imm
  | Osym      of string * int
  | Otbl      of Bv.t
  | Ounop     of Insn.unop
  | Ovaarg    of Var.t * Type.arg
  | Ovar      of Var.t
  | Ovastart  of Label.t
[@@deriving compare, equal, hash, sexp]

type t =
  | N of op * Id.t list
  | U of {pre : Id.t; post : Id.t}
[@@deriving compare, equal, hash, sexp]

let is_const = function
  | N (Obool _, [])
  | N (Oint _, [])
  | N (Odouble _, [])
  | N (Osingle _, [])
  | N (Osym _, []) -> true
  | N _ | U _ -> false

let commute = function
  | N (Obinop b, [x; y]) ->
    begin match b with
      | `add _
      | `mul _
      | `mulh _
      | `umulh _
      | `and_ _
      | `or_ _
      | `xor _
      | `eq _
      | `ne _ -> Some (N (Obinop b, [y; x]))
      | _ -> None
    end
  | N _ | U _ -> None

let of_const : const -> t = function
  | `bool b -> N (Obool b, [])
  | `int (i, t) -> N (Oint (i, t), [])
  | `double d -> N (Odouble d, [])
  | `float s -> N (Osingle s, [])
  | `sym (s, o) -> N (Osym (s, o), [])

let infer_ty_binop : Virtual.Insn.binop -> Type.t option = function
  | `add t
  | `div t
  | `mul t
  | `sub t -> Some (t :> Type.t)
  | `rem t
  | `mulh t
  | `udiv t
  | `umulh t
  | `urem t
  | `and_ t
  | `or_ t
  | `asr_ t
  | `lsl_ t
  | `lsr_ t
  | `rol t
  | `ror t
  | `xor t -> Some (t :> Type.t)
  | #Virtual.Insn.cmp -> Some `flag

let infer_ty_unop : Virtual.Insn.unop -> Type.t option = function
  | `neg t
  | `copy t -> Some (t :> Type.t)
  | `clz t
  | `ctz t
  | `not_ t
  | `popcnt t
  | `flag t
  | `ftosi (_, t)
  | `ftoui (_, t)
  | `itrunc t
  | `sext t
  | `zext t -> Some (t :> Type.t)
  | `ifbits t -> Some (t :> Type.t)
  | `fext t
  | `fibits t
  | `ftrunc t
  | `sitof (_, t)
  | `uitof (_, t) -> Some (t :> Type.t)

let infer_ty ~tid ~tty ~tvar ~word : t -> Type.t option = function
  | U {pre; post} ->
    let tpre = tid pre in
    let tpost = tid post in
    Option.merge tpre tpost ~f:(fun x y ->
        assert (Type.equal x y);
        x)
  | N (o, _) -> match o with
    | Oaddr _ -> Some word
    | Obinop b -> infer_ty_binop b
    | Obool _ -> Some `flag
    | Obr -> None
    | Ocall0 _ -> None
    | Ocall (_, `name n) -> tty n
    | Ocall (_, (#Type.basic as t)) -> Some (t :> Type.t)
    | Ocall (_, `si8) -> Some `i8
    | Ocall (_, `si16) -> Some `i16
    | Ocall (_, `si32) -> Some `i32
    | Ocallargs -> None
    | Odouble _ -> Some `f64
    | Ojmp -> None
    | Oint (_, t) -> Some (t :> Type.t)
    | Oload (_, (#Type.basic as t)) -> Some (t :> Type.t)
    | Oload (_, `name s) -> tty s
    | Olocal _ -> None
    | Oret -> None
    | Osel t -> Some (t :> Type.t)
    | Oset _ -> None
    | Osingle _ -> Some `f32
    | Ostore _ -> None
    | Osw _ -> None
    | Osym _ -> Some word
    | Otbl _ -> None
    | Ounop u -> infer_ty_unop u
    | Ovaarg (_, (#Type.basic as t)) -> Some (t :> Type.t)
    | Ovaarg (_, `name n) -> tty n
    | Ovar x -> tvar x
    | Ovastart _ -> None

module Eval = struct
  open Virtual.Eval

  let go op args = match op, args with
    | Oaddr _, _ -> None
    | Obinop o, [Some `int (a, _); Some `int (b, _)] ->
      (binop_int o a b :> const option)
    | Obinop o, [Some `float a; Some `float b] ->
      (binop_single o a b :> const option)
    | Obinop o, [Some `double a; Some `double b] ->
      (binop_double o a b :> const option)
    | Obinop _, _ -> None
    | Obool b, [] -> Some (`bool b)
    | Obool _, _ -> None
    | Obr, _ -> None
    | Ocall0 _, _ -> None
    | Ocall _, _ -> None
    | Ocallargs, _ -> None
    | Odouble d, [] -> Some (`double d)
    | Odouble _, _ -> None
    | Ojmp, _ -> None
    | Oint (i, t), [] -> Some (`int (i, t))
    | Oint _, _ -> None
    | Oload _, _ -> None
    | Olocal _, _ -> None
    | Oret, _ -> None
    | Oset _, _ -> None
    | Osel _, [Some `bool true;  t; _] -> t
    | Osel _, [Some `bool false; _; f] -> f
    | Osel _, _ -> None
    | Osingle s, [] -> Some (`float s)
    | Osingle _, _ -> None
    | Ostore _, _ -> None
    | Osw _, _ -> None
    | Osym (s, o), [] -> Some (`sym (s, o))
    | Osym _, _ -> None
    | Otbl _, _ -> None
    | Ounop o, [Some `int (a, ty)] ->
      (unop_int o a ty :> const option)
    | Ounop o, [Some `float a] ->
      (unop_single o a :> const option)
    | Ounop o, [Some `double a] ->
      (unop_double o a :> const option)
    | Ounop `flag t, [Some `bool b] -> Some (`int (Bv.bool b, t))
    | Ounop _, _ -> None
    | Ovaarg _, _ -> None
    | Ovar _, _ -> None
    | Ovastart _, _ -> None
end

let rec const ~node n : const option = match n with
  | N (Obool b, []) -> Some (`bool b)
  | N (Oint (i, t), []) -> Some (`int (i, t))
  | N (Odouble d, []) -> Some (`double d)
  | N (Osingle s, []) -> Some (`float s)
  | N (Osym (s, o), []) -> Some (`sym (s, o))
  | N _ -> None
  | U {pre; post} ->
    let a = const ~node @@ node pre in
    let b = const ~node @@ node post in
    Option.merge a b ~f:(fun a b ->
        assert (equal_const a b);
        a)

let rec eval ~node n : const option = match n with
  | N (op, children) ->
    let cs = List.map children ~f:(fun c ->
        const ~node @@ node c) in
    Eval.go op cs
  | U {pre; post} ->
    let a = eval ~node @@ node pre in
    let b = eval ~node @@ node post in
    Option.merge a b ~f:(fun a b ->
        assert (equal_const a b);
        a)

let pp_op ppf = function
  | Oaddr a ->
    Format.fprintf ppf "addr:%a" Bv.pp a
  | Obinop b ->
    Format.fprintf ppf "%a" Insn.pp_binop b
  | Obool b ->
    Format.fprintf ppf "%a" Bool.pp b
  | Obr ->
    Format.fprintf ppf "br"
  | Ocall0 _ ->
    Format.fprintf ppf "call"
  | Ocall (_, ((#Type.basic | `si8 | `si16 | `si32) as t)) ->
    Format.fprintf ppf "call.%a" Type.pp_ret t
  | Ocall (_, `name n) ->
    Format.fprintf ppf "call:%s" n
  | Ocallargs ->
    Format.fprintf ppf "callargs"
  | Odouble d ->
    Format.fprintf ppf "%a_d" Float.pp d
  | Ojmp ->
    Format.fprintf ppf "jmp"
  | Oint (i, t) ->
    Format.fprintf ppf "%a_%a" Bv.pp i Type.pp_imm t
  | Oload (x, (#Type.basic as t)) ->
    Format.fprintf ppf "ld.%a:%a" Type.pp_basic t Var.pp x
  | Oload (x, `name n) ->
    Format.fprintf ppf "ld:%s:%a" n Var.pp x
  | Olocal l ->
    Format.fprintf ppf "%a" Label.pp l
  | Oret ->
    Format.fprintf ppf "ret"
  | Osel t ->
    Format.fprintf ppf "sel.%a" Type.pp_basic t
  | Oset x ->
    Format.fprintf ppf "set:%a" Var.pp x
  | Osingle s ->
    Format.fprintf ppf "%s_s" @@ Float32.to_string s
  | Ostore ((#Type.basic as t), _) ->
    Format.fprintf ppf "st.%a" Type.pp_basic t
  | Ostore (`name n, _) ->
    Format.fprintf ppf "st:%s" n
  | Osw t ->
    Format.fprintf ppf "sw.%a" Type.pp_imm t
  | Osym (s, 0) ->
    Format.fprintf ppf "$%s" s
  | Osym (s, o) when o > 0 ->
    Format.fprintf ppf "$%s+%d" s o
  | Osym (s, o) ->
    Format.fprintf ppf "$%s-%d" s (lnot o + 1)
  | Otbl i ->
    Format.fprintf ppf "tbl:%a" Bv.pp i
  | Ounop u ->
    Format.fprintf ppf "%a" Insn.pp_unop u
  | Ovaarg (_, (#Type.basic as t)) ->
    Format.fprintf ppf "vaarg.%a" Type.pp_basic t
  | Ovaarg (_, `name n) ->
    Format.fprintf ppf "vaarg:%s" n
  | Ovar x ->
    Format.fprintf ppf "%a" Var.pp x
  | Ovastart _ ->
    Format.fprintf ppf "vastart"

let rec pp ?node ppf n =
  let pp_child = match node with
    | None -> Id.pp
    | Some f -> fun ppf id ->
      pp ?node ppf @@ f id in
  match n with
  | N (op, []) -> Format.fprintf ppf "%a" pp_op op
  | N (op, cs) ->
    let pp_sep ppf () = Format.fprintf ppf " " in
    Format.fprintf ppf "(%a %a)" pp_op op
      (Format.pp_print_list ~pp_sep pp_child) cs
  | U {pre; post} ->
    Format.fprintf ppf "(union %a %a)" pp_child pre pp_child post
