open Core
open Regular.Std
open Common

module Table = struct
  type t = local Map.M(Bitvec).t [@@deriving bin_io, compare, equal, sexp]

  let create_exn l = try Map.of_alist_exn (module Bitvec) l with
    | exn -> invalid_argf "%s" (Exn.to_string exn) ()

  let create l = Or_error.try_with @@ fun () -> create_exn l
  let enum t = Map.to_sequence t
  let find t v = Map.find t v

  let map_exn t ~f = try
      Map.to_sequence t |>
      Seq.map ~f:(fun (v, l) -> f v l) |>
      Map.of_sequence_exn (module Bitvec)
    with exn -> invalid_argf "%s" (Exn.to_string exn) ()

  let map t ~f = Or_error.try_with @@ fun () -> map_exn t ~f

  let free_vars t =
    Map.fold t ~init:Var.Set.empty ~f:(fun ~key:_ ~data s ->
        Set.union s @@ free_vars_of_local data)

  let pp_elt ppl ppf (v, l) =
    Format.fprintf ppf "%a -> %a" Bitvec.pp v ppl l

  let pp ppf t =
    let pp_sep ppf () = Format.fprintf ppf ",@;" in
    Format.pp_print_list ~pp_sep (pp_elt pp_local) ppf (Map.to_alist t)
end

type table = Table.t [@@deriving bin_io, compare, equal, sexp]

type t = [
  | `hlt
  | `jmp of dst
  | `br  of Var.t * dst * dst
  | `ret of operand option
  | `sw  of Type.imm * Var.t * local * table
] [@@deriving bin_io, compare, equal, sexp]

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
      Var.Set.singleton x;
      free_vars_of_local d;
      Table.free_vars tbl;
    ]

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
      Type.pp_imm t Var.pp x pp_local ld Table.pp tbl
