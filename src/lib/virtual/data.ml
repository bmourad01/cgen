open Core
open Regular.Std
open Common

type elt = [
  | const
  | `string of string
  | `zero   of int
] [@@deriving bin_io, compare, equal, sexp]

let pp_elt ppf : elt -> unit = function
  | #const as c -> Format.fprintf ppf "%a" pp_const c
  | `string s -> Format.fprintf ppf "\"%s\"" s
  | `zero n -> Format.fprintf ppf "z %d" n

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
        | `int (_, t) -> `elt ((t :> Type.basic), 1)
        | `float _ -> `elt (`f32, 1)
        | `double _ -> `elt (`f64, 1)
        | `string s -> `elt (`i8, String.length s + 1)
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
