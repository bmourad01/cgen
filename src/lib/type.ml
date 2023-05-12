open Core
open Regular.Std

type imm_base = [
  | `i32
  | `i64
] [@@deriving bin_io, compare, equal, hash, sexp]

let sizeof_imm_base : imm_base -> int = function
  | `i32 -> 32
  | `i64 -> 64

let pp_imm_base ppf : imm_base -> unit = function
  | `i32 -> Format.fprintf ppf "w"
  | `i64 -> Format.fprintf ppf "l"

type imm = [
  | `i8
  | `i16
  | imm_base
] [@@deriving bin_io, compare, equal, hash, sexp]

let sizeof_imm : imm -> int = function
  | `i8 -> 8
  | `i16 -> 16
  | #imm_base as b -> sizeof_imm_base b

let pp_imm ppf : imm -> unit = function
  | `i8  -> Format.fprintf ppf "b"
  | `i16 -> Format.fprintf ppf "h"
  | #imm_base as i -> pp_imm_base ppf i

type fp = [
  | `f32
  | `f64
] [@@deriving bin_io, compare, equal, hash, sexp]

let sizeof_fp : fp -> int = function
  | `f32 -> 32
  | `f64 -> 32

let pp_fp ppf : fp -> unit = function
  | `f32 -> Format.fprintf ppf "s"
  | `f64 -> Format.fprintf ppf "d"

type basic = [
  | imm
  | fp
] [@@deriving bin_io, compare, equal, hash, sexp]

let sizeof_basic : basic -> int = function
  | #imm as i -> sizeof_imm i
  | #fp  as f -> sizeof_fp  f

let pp_basic ppf : basic -> unit = function
  | #imm as i -> Format.fprintf ppf "%a" pp_imm i
  | #fp  as f -> Format.fprintf ppf "%a" pp_fp f

type field = [
  | `elt  of basic  * int
  | `name of string * int
] [@@deriving bin_io, compare, equal, hash, sexp]

let pp_field ppf : field -> unit = function
  | `elt  (t, 1) -> Format.fprintf ppf "%a" pp_basic t
  | `elt  (t, n) -> Format.fprintf ppf "%a %d" pp_basic t n
  | `name (s, 1) -> Format.fprintf ppf ":%s" s
  | `name (s, n) -> Format.fprintf ppf ":%s %d" s n

type compound = [
  | `compound of string * int option * field list
  | `opaque   of string * int * int
] [@@deriving bin_io, compare, equal, hash, sexp]

let compound_name : compound -> string = function
  | `compound (s, _, _)
  | `opaque (s, _, _) -> s

type datum = [
  | basic
  | `pad    of int
  | `opaque of int
] [@@deriving bin_io, compare, equal, hash, sexp]

let pp_datum ppf : datum -> unit = function
  | #basic as b -> Format.fprintf ppf "%a"  pp_basic b
  | `pad n      -> Format.fprintf ppf "%d"  n
  | `opaque n   -> Format.fprintf ppf "?%d" n

type layout = {
  align : int;
  data  : datum list;
} [@@deriving bin_io, compare, equal, hash, sexp]

let pp_layout ppf l =
  let pp_sep ppf () = Format.fprintf ppf ", " in
  Format.fprintf ppf "%d(%a)" l.align
    (Format.pp_print_list ~pp_sep pp_datum) l.data

let sizeof_layout l = List.fold l.data ~init:0 ~f:(fun sz -> function
    | #basic as b -> sz + sizeof_basic b
    | `pad n | `opaque n -> sz + n * 8)

let padding size align =
  (align - size mod align) mod align

(* pre: the list is accumulated in reverse *)
let padded data = function
  | 0 -> data | p -> `pad p :: data

(* pre: the list is accumulated in reverse *)
let coalesce =
  let rec aux acc = function
    | [] -> acc
    | `pad a :: `pad b :: ds ->
      aux acc @@ `pad (a + b) :: ds
    | `opaque a :: `opaque b :: ds ->
      aux acc @@ `opaque (a + b) :: ds
    | d :: ds -> aux (d :: acc) ds in
  aux []

let layout gamma : compound -> layout = function
  | `opaque (s, n, _) | `compound (s, Some n, _) when n <= 0 ->
    invalid_argf "Invalid alignment %d for type :%s" n s ()
  | `opaque (s, _, n) when n < 0 ->
    invalid_argf "Invalid number of bytes %d for opaque type :%s" n s ()
  | `opaque (_, align, 0) -> {align; data = [`pad align]}
  | `opaque (_, align, n) ->
    {align; data = padded [`opaque n] @@ padding n align}
  | `compound (_, Some n, []) -> {align = n; data = [`pad n]}
  | `compound (_, None, []) -> {align = 1; data = [`pad 1]}
  | `compound (name, align, fields) ->
    let data, align, size =
      let init = [], Option.value align ~default:1, 0 in
      List.fold fields ~init ~f:(fun (data, align, size) f ->
          let fdata, falign, fsize = match f with
            | `elt (_, c) | `name (_, c) when c <= 0 ->
              invalid_argf "Invalid field %s for type :%s"
                (Format.asprintf "%a" pp_field f) name ()
            | `elt (t, c) ->
              let s = sizeof_basic t / 8 in
              let d = List.init c ~f:(fun _ -> (t :> datum)) in
              d, s, s * c
            | `name (s, c) -> match gamma s with
              | {align = a; _} when a <= 0 ->
                invalid_argf "Invalid alignment %d for type :%s" a s ()
              | {align; data} as l ->
                let data = List.init c ~f:(fun _ -> data) |> List.concat in
                data, align, (sizeof_layout l / 8) * c in
          let align = max align falign in
          let pad = padding size align in
          let data = List.rev_append fdata @@ padded data pad in
          data, align, size + pad + fsize) in
    {align; data = coalesce @@ padded data @@ padding size align}

let pp_compound ppf : compound -> unit = function
  | `compound (_, align, fields) ->
    let pp_sep ppf () = Format.fprintf ppf ",@;" in
    Option.iter align ~f:(Format.fprintf ppf "align %d ");
    Format.fprintf ppf "{@;@[<v 2>%a@]@;}"
      (Format.pp_print_list ~pp_sep pp_field) fields
  | `opaque (_, align, n) ->
    Format.fprintf ppf "align %d {%d}" align n

let pp_compound_decl ppf : compound -> unit = function
  | `compound (name, align, fields) ->
    let pp_sep ppf () = Format.fprintf ppf ",@;" in
    Format.fprintf ppf "type :%s = " name;
    Option.iter align ~f:(Format.fprintf ppf "align %d ");
    Format.fprintf ppf "{@;@[<v 2>  %a@]@;}"
      (Format.pp_print_list ~pp_sep pp_field) fields
  | `opaque (name, align, n) ->
    Format.fprintf ppf "type :%s = align %d {%d}" name align n

type special = [
  | `flag
] [@@deriving bin_io, compare, equal, hash, sexp]

let pp_special ppf : special -> unit = function
  | `flag -> Format.fprintf ppf "f"

type arg = [
  | basic
  | `name of string
] [@@deriving bin_io, compare, equal, hash, sexp]

let pp_arg ppf : arg -> unit = function
  | #basic as b -> Format.fprintf ppf "%a" pp_basic b
  | `name s -> Format.fprintf ppf ":%s" s

type proto = [
  | `proto of basic option * arg list * bool
] [@@deriving bin_io, compare, equal, hash, sexp]

let pp_proto ppf : proto -> unit = function
  | `proto (ret, args, variadic) ->
    let pp_sep ppf () = Format.fprintf ppf ", " in
    let pp_args = Format.pp_print_list ~pp_sep pp_arg in
    Option.iter ret ~f:(Format.fprintf ppf "%a " pp_basic);
    Format.fprintf ppf "(%a" pp_args args;
    match variadic, args with
    | false, _ -> Format.fprintf ppf ")"
    | true, [] -> Format.fprintf ppf "...)"
    | true, _  -> Format.fprintf ppf ", ...)"

module T = struct
  type t = [
    | basic
    | compound
    | special
  ] [@@deriving bin_io, compare, equal, hash, sexp]
end

include T

let pp ppf : t -> unit = function
  | #basic    as b -> Format.fprintf ppf "%a" pp_basic b
  | #compound as c -> Format.fprintf ppf "%a" pp_compound c
  | #special  as s -> Format.fprintf ppf "%a" pp_special s

include Regular.Make(struct
    include T

    let pp = pp
    let version = "0.1"
    let module_name = Some "Cgen.Type"
  end)
