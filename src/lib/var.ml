open Core
open Regular.Std

type id = Int63.t [@@deriving bin_io, compare, equal, hash, sexp]

type ident =
  | Temp of id
  | Name of string
[@@deriving bin_io, compare, equal, hash, sexp]

module T = struct
  type t = {
    ident : ident;
    index : int;
    typ   : Type.t;
  } [@@deriving bin_io, compare, equal, hash, sexp]
end

include T

let is_temp x = match x.ident with
  | Temp _ -> true
  | Name _ -> false

let is_named x = match x.ident with
  | Temp _ -> false
  | Name _ -> true

let name x = match x.ident with
  | Temp _ -> None
  | Name n -> Some n

let index x = x.index
let typ x = x.typ
let with_index x index = {x with index}
let base x = with_index x 0

let same x y = match x.ident, y.ident with
  | Temp ix, Temp iy -> Int63.(ix = iy)
  | Name nx, Name ny -> String.(nx = ny)
  | _ -> false

let create ?(index = 0) name typ = {ident = Name name; index; typ}
let temp ?(index = 0) id typ = {ident = Temp id; index; typ}

let pp ppf x = match x.ident with
  | Temp id when x.index = 0 -> Format.fprintf ppf "#%a" Int63.pp id
  | Temp id -> Format.fprintf ppf "#%a.%u" Int63.pp id x.index
  | Name n when x.index = 0 -> Format.fprintf ppf "%s" n
  | Name n -> Format.fprintf ppf "%s.%u" n x.index

let mem = create "mem" `mem

include Regular.Make(struct
    include T
    let pp = pp
    let version = "0.1"
    let hash = hash
    let module_name = Some "Cgen.Var"
  end)
