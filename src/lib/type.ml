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
  | `elt  of basic * int
  | `name of string
] [@@deriving bin_io, compare, equal, hash, sexp]

let pp_field ppf : field -> unit = function
  | `elt (t, 1) -> Format.fprintf ppf "%a" pp_basic t
  | `elt (t, n) -> Format.fprintf ppf "%a %d" pp_basic t n
  | `name s     -> Format.fprintf ppf ":%s" s

type compound = [
  | `compound of string * int option * field list
] [@@deriving bin_io, compare, equal, hash, sexp]

type datum = [
  | `full of basic
  | `pad of basic * int
] [@@deriving bin_io, compare, equal, hash, sexp]

let sizeof_layout : datum list -> int =
  List.fold ~init:0 ~f:(fun sz -> function
      | `full t -> sz + sizeof_basic t
      | `pad (t, n) -> sz + + sizeof_basic t + n * 8)

let padding off align = (align - off mod align) mod align

let layout gamma : compound -> datum list = function
  | `compound (_, _, []) -> []
  | `compound (_, Some n, _) when n <= 0 ->
    invalid_argf "Invalid alignment %d" n ()
  | `compound (_, align, fields) ->
    let layout = List.concat_map fields ~f:(function
        | `elt (t, n) ->
          let e = `full t in
          List.init n ~f:(fun _ -> e)
        | `name n -> gamma n) in
    let align = match align with
      | Some align -> align * 8
      | None -> List.fold layout ~init:8 ~f:(fun align -> function
          | `full t | `pad (t, _) -> max align @@ sizeof_basic t) in
    let off, seq = List.fold layout ~init:(0, []) ~f:(fun (off, seq) elt ->
        let fsize = match elt with
          | `full t -> sizeof_basic t
          | `pad (t, n) -> sizeof_basic t + n * 8 in
        let pad = padding off align in
        let off = off + fsize + pad in
        let seq = match pad with
          | 0 -> elt :: seq
          | _ -> match elt with
            | `full t -> `pad (t, pad / 8) :: seq
            | `pad (t, n) -> `pad (t, n + pad / 8) :: seq in
        off, seq) in
    let seq = match padding off align with
      | 0 -> seq
      | n -> match seq with
        | [] -> seq
        | `full t :: rest -> `pad (t, n / 8) :: rest
        | `pad (t, m) :: rest -> `pad (t, m + n / 8) :: rest in
    List.rev seq

let pp_compound ppf : compound -> unit = function
  | `compound (_, align, fields) ->
    let pp_sep ppf () = Format.fprintf ppf ",@;" in
    Option.iter align ~f:(Format.fprintf ppf "align %d ");
    Format.fprintf ppf "{@;@[<v 2>%a@]@;}"
      (Format.pp_print_list ~pp_sep pp_field) fields

let pp_compound_decl ppf : compound -> unit = function
  | `compound (name, align, fields) ->
    let pp_sep ppf () = Format.fprintf ppf ",@;" in
    Format.fprintf ppf "type :%s = " name;
    Option.iter align ~f:(Format.fprintf ppf "align %d ");
    Format.fprintf ppf "{@;@[<v 2>  %a@]@;}"
      (Format.pp_print_list ~pp_sep pp_field) fields

type special = [
  | `mem 
  | `flag
] [@@deriving bin_io, compare, equal, hash, sexp]

let pp_special ppf : special -> unit = function
  | `mem  -> Format.fprintf ppf "m"
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
