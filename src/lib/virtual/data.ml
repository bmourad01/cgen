open Core
open Regular.Std
open Common

type elt = [
  | `basic  of Type.basic * const list
  | `string of string
  | `zero   of int
  | `sym    of string * int
] [@@deriving bin_io, compare, equal, sexp]

let pp_elt ppf : elt -> unit = function
  | `basic (t, cs) ->
    let pp_sep ppf () = Format.fprintf ppf " " in
    Format.fprintf ppf "%a %a"
      Type.pp_basic t
      (Format.pp_print_list ~pp_sep pp_const) cs
  | `string s -> Format.fprintf ppf "%a \"%s\"" Type.pp_basic `i8 s
  | `zero n -> Format.fprintf ppf "z %d" n
  | `sym (s, 0) -> Format.fprintf ppf "$%s" s
  | `sym (s, n) when n > 0 -> Format.fprintf ppf "$%s+0x%x" s n
  | `sym (s, n) -> Format.fprintf ppf "$%s-0x%x" s (lnot n + 1)

module T = struct
  type t = {
    name    : string;
    elts    : elt array;
    linkage : Linkage.t;
    align   : int option;
  } [@@deriving bin_io, compare, equal, sexp]
end

include T

let create_exn
    ?(align = None)
    ?(linkage = Linkage.default_export)
    ~name
    ~elts
    () =
  match Array.of_list elts with
  | [||] -> invalid_argf "Cannot create empty data %s" name ()
  | elts ->
    Array.iter elts ~f:(function
        | `basic (t, []) -> invalid_arg @@ Format.asprintf
            "In data $%s: `basic field of type %a is uninitialized"
            name Type.pp_basic t
        | _ -> ());
    Option.iter align ~f:(function
        | n when n < 1 ->
          invalid_argf "In data $%s: invalid alignment %d" name n ()
        | _ -> ());
    {name; elts; linkage; align}

let create
    ?(align = None)
    ?(linkage = Linkage.default_export)
    ~name
    ~elts
    () =
  Or_error.try_with @@ create_exn ~name ~elts ~linkage ~align

let name d = d.name
let elts ?(rev = false) d = Array.enum d.elts ~rev
let linkage d = d.linkage
let align d = d.align
let has_name d name = String.(name = d.name)
let hash d = String.hash d.name

let typeof d target =
  let word = (Target.word target :> Type.basic) in
  let name = Format.sprintf "%s_t" d.name in
  let fields = Array.fold_right d.elts ~init:[] ~f:(fun elt fields ->
      let t = match elt with
        | `basic (t, cs) -> `elt (t, List.length cs)
        | `string s -> `elt (`i8, String.length s)
        | `zero n -> `elt (`i8, n)
        | `sym _ -> `elt (word, 1) in
      t :: fields) in
  `compound (name, d.align, fields)

let prepend_elt d e = {
  d with elts = Array.push_front d.elts e;
}

let append_elt d e = {
  d with elts = Array.push_back d.elts e;
}

let map_elts d ~f = {
  d with elts = Array.map d.elts ~f;
}

let pp ppf d =
  let sep ppf = Format.fprintf ppf ",@;" in
  if Linkage.export d.linkage
  || Linkage.section d.linkage |> Option.is_some then
    Format.fprintf ppf "%a " Linkage.pp d.linkage;
  Format.fprintf ppf "data $%s = " d.name;
  Option.iter d.align ~f:(Format.fprintf ppf "align %d ");
  Format.fprintf ppf "{@;@[<v 2>  %a@]@;}"
    (Array.pp pp_elt sep) d.elts

include Regular.Make(struct
    include T
    let module_name = Some "Cgen.Virtual.Data"
    let version = "0.1"
    let pp = pp
    let hash = hash
  end)
