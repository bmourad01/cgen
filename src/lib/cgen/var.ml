open Core
open Regular.Std
open Cgen_containers

type t = int [@@deriving bin_io, compare, equal, hash, sexp]

let of_int_unsafe v = v

let pp ppf v = Format.fprintf ppf "%%%d" v

include Regular.Make(struct
    type nonrec t = t [@@deriving bin_io, compare, equal, hash, sexp]
    let pp = pp
    let version = "0.1"
    let module_name = Some "Cgen.Var"
  end)

module Patricia_key = struct
  include Int
  let size = 63
  let equal : t -> t -> bool = phys_equal
end

module Dense_key = struct
  type nonrec t = t
  let empty_sentinel = -1
  let to_int v = v
  let pp = pp
  let equal : t -> t -> bool = phys_equal
end

module Tree = Patricia_tree.Make(Patricia_key)
module Tree_set = Patricia_tree.Make_set(Patricia_key)
module Dense_table = Dense.Make_map(Dense_key)
module Dense_set = Dense.Make_set(Dense_key)
