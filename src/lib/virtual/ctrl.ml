open Core
open Regular.Std
open Common

module Table = struct
  type t = {
    tbl : local Map.M(Bv).t;
    typ : Type.imm;
  } [@@deriving bin_io, compare, equal, sexp]

  let create_exn l t = try {
    tbl = Map.of_alist_exn (module Bv) l;
    typ = t;
  } with exn -> invalid_argf "%s" (Exn.to_string exn) ()

  let create l t = Or_error.try_with @@ fun () -> create_exn l t
  let enum t = Map.to_sequence t.tbl
  let find t v = Map.find t.tbl v
  let typ t = t.typ

  let map_exn t ~f = try
      Map.to_sequence t.tbl |>
      Seq.map ~f:(fun (v, l) -> f v l) |>
      Map.of_sequence_exn (module Bv) |>
      fun tbl -> {t with tbl}
    with exn -> invalid_argf "%s" (Exn.to_string exn) ()

  let map t ~f = Or_error.try_with @@ fun () -> map_exn t ~f

  let free_vars t =
    Map.fold t.tbl ~init:Var.Set.empty ~f:(fun ~key:_ ~data s ->
        Set.union s @@ free_vars_of_local data)

  let pp_elt t ppl ppf (v, l) =
    Format.fprintf ppf "%a_%a -> %a" Bv.pp v Type.pp_imm t ppl l

  let pp ppf t =
    let pp_sep ppf () = Format.fprintf ppf ",@;" in
    Format.pp_print_list ~pp_sep (pp_elt t.typ pp_local)
      ppf (Map.to_alist t.tbl)
end

type table = Table.t [@@deriving bin_io, compare, equal, sexp]

type swindex = [
  | `var of Var.t
  | `sym of string * int
] [@@deriving bin_io, compare, equal, sexp]

let pp_swindex ppf = function
  | `var x -> Format.fprintf ppf "%a" Var.pp x
  | `sym (s, 0) -> Format.fprintf ppf "$%s" s
  | `sym (s, n) when n > 0 -> Format.fprintf ppf "$%s+0x%x" s n
  | `sym (s, n) -> Format.fprintf ppf "$%s-0x%x" s (lnot n + 1)

let var_of_swindex = function
  | `var x -> Some x
  | `sym _ -> None

type t = [
  | `hlt
  | `jmp of dst
  | `br  of Var.t * dst * dst
  | `ret of operand option
  | `sw  of Type.imm * swindex * local * table
  | `tcall of Type.basic option * global * operand list * operand list
] [@@deriving bin_io, compare, equal, sexp]

let pp_tcall_res ppf = function
  | None -> Format.fprintf ppf "tcall "
  | Some t ->
    Format.fprintf ppf "tcall.%a " Type.pp_basic t

let pp_tcall ppf c =
  let res, dst, args, vargs = match c with
    | `tcall (Some _ as t, d, a, va) -> t, d, a, va
    | `tcall (None, d, a, va) -> None, d, a, va in
  Format.fprintf ppf "%a%a(%a%a)"
    pp_tcall_res res
    pp_global dst
    Insn.pp_call_args args
    (Insn.pp_call_vargs args) vargs

let free_vars : t -> Var.Set.t = function
  | `hlt -> Var.Set.empty
  | `jmp d -> free_vars_of_dst d
  | `br (x, y, n) -> Var.Set.union_list [
      Var.Set.singleton x;
      free_vars_of_dst y;
      free_vars_of_dst n;
    ]
  | `ret None -> Var.Set.empty
  | `ret (Some a) -> var_set_of_option @@ var_of_operand a
  | `sw (_, x, d, tbl) -> Var.Set.union_list [
      var_set_of_option @@ var_of_swindex x;
      free_vars_of_local d;
      Table.free_vars tbl;
    ]
  | `tcall (_, f, args, vargs) ->
    let f = var_of_global f |> Option.to_list |> Var.Set.of_list in
    let args = List.filter_map args ~f:var_of_operand |> Var.Set.of_list in
    let vargs = List.filter_map vargs ~f:var_of_operand |> Var.Set.of_list in
    Var.Set.union_list [f; args; vargs]

let pp ppf : t -> unit = function
  | `hlt -> Format.fprintf ppf "hlt"
  | `jmp d ->
    Format.fprintf ppf "jmp %a" pp_dst d
  | `br (c, t, f) ->
    Format.fprintf ppf "br %a, %a, %a" Var.pp c pp_dst t pp_dst f
  | `ret (Some x) ->
    Format.fprintf ppf "ret %a" pp_operand x
  | `ret None ->
    Format.fprintf ppf "ret"
  | `sw (t, x, ld, tbl) ->
    Format.fprintf ppf "sw.%a %a, %a [@[<v 0>%a@]]"
      Type.pp_imm t pp_swindex x pp_local ld Table.pp tbl
  | `tcall _ as c ->
    Format.fprintf ppf "%a" pp_tcall c
