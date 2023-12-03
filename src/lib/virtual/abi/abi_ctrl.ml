open Core
open Abi_common

module Table = struct
  type t = {
    tbl : local Map.M(Bv).t;
    typ : Type.imm;
  } [@@deriving bin_io, compare, equal, sexp]

  let create_exn l t = match Map.of_alist (module Bv) l with
    | `Ok tbl -> {tbl; typ = t}
    | `Duplicate_key v ->
      invalid_argf
        "Cannot create switch table with duplicate index: %s_%s"
        (Bv.to_string v) (Format.asprintf "%a" Type.pp_imm t) ()

  let create l t = try Ok (create_exn l t) with
    | Invalid_argument msg -> Or_error.error_string msg

  let enum t = Map.to_sequence t.tbl
  let length t = Map.length t.tbl
  let find t v = Map.find t.tbl v
  let typ t = t.typ

  let map_exn t ~f =
    Map.to_sequence t.tbl |>
    Sequence.map ~f:(fun (v, l) -> f v l) |>
    Map.of_sequence (module Bv) |> function
    | `Ok tbl -> {t with tbl}
    | `Duplicate_key v ->
      invalid_argf
        "Cannot map switch table with duplicate index: %s_%s"
        (Bv.to_string v) (Format.asprintf "%a" Type.pp_imm t.typ) ()

  let map t ~f = try Ok (map_exn t ~f) with
    | Invalid_argument msg -> Or_error.error_string msg

  let free_vars t =
    let init = Set.empty (module Var_comparator) in
    Map.fold t.tbl ~init ~f:(fun ~key:_ ~data s ->
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
  | `var of var
  | `sym of string * int
] [@@deriving bin_io, compare, equal, sexp]

let pp_swindex ppf = function
  | `var x -> Format.fprintf ppf "%a" pp_var x
  | `sym (s, 0) -> Format.fprintf ppf "$%s" s
  | `sym (s, n) when n > 0 -> Format.fprintf ppf "$%s+0x%x" s n
  | `sym (s, n) -> Format.fprintf ppf "$%s-0x%x" s (lnot n + 1)

let var_of_swindex = function
  | `var x -> Some x
  | `sym _ -> None

type t = [
  | `hlt
  | `jmp of dst
  | `br  of var * dst * dst
  | `ret of string list
  | `sw  of Type.imm * swindex * local * table
] [@@deriving bin_io, compare, equal, sexp]

let free_vars : t -> (var, var_comparator) Set.t = function
  | `hlt -> Set.empty (module Var_comparator)
  | `jmp d -> free_vars_of_dst d
  | `br (x, y, n) ->
    Set.union_list (module Var_comparator) [
      Set.singleton (module Var_comparator) x;
      free_vars_of_dst y;
      free_vars_of_dst n;
    ]
  | `ret xs ->
    let init = Set.empty (module Var_comparator) in
    List.fold xs ~init ~f:(fun s r -> Set.add s @@ `reg r)
  | `sw (_, x, d, tbl) ->
    Set.union_list (module Var_comparator) [
      var_set_of_option @@ var_of_swindex x;
      free_vars_of_local d;
      Table.free_vars tbl;
    ]

let pp ppf : t -> unit = function
  | `hlt -> Format.fprintf ppf "hlt"
  | `jmp d ->
    Format.fprintf ppf "jmp %a" pp_dst d
  | `br (c, t, f) ->
    Format.fprintf ppf "br %a, %a, %a" pp_var c pp_dst t pp_dst f
  | `ret [] ->
    Format.fprintf ppf "ret"
  | `ret xs ->
    let pp_sep ppf () = Format.fprintf ppf ", " in
    Format.fprintf ppf "ret %a"
      (Format.pp_print_list ~pp_sep String.pp) xs
  | `sw (t, x, ld, tbl) ->
    Format.fprintf ppf "sw.%a %a, %a [@[<v 0>%a@]]"
      Type.pp_imm t pp_swindex x pp_local ld Table.pp tbl
