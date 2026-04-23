open Core
open Regular.Std
open Cgen_containers

type t = Int63.t [@@deriving bin_io, compare, equal, hash, sexp]

let pp ppf v = Format.fprintf ppf "%%%a" Int63.pp v

include Regular.Make(struct
    type nonrec t = t [@@deriving bin_io, compare, equal, hash, sexp]
    let pp = pp
    let version = "0.1"
    let module_name = Some "Cgen.Var"
  end)

module Patricia_key = struct
  include Int63
  let size = 63
  let to_int = to_int_trunc
end

module Dense_key = struct
  type nonrec t = t [@@deriving equal]
  let empty_sentinel = Int63.of_int (-1)
  let to_int = Int63.to_int_trunc
  let pp = pp
end

module Tree = Patricia_tree.Make(Patricia_key)
module Tree_set = Patricia_tree.Make_set(Patricia_key)
module Dense_table = Dense.Make_map(Dense_key)
module Dense_set = Dense.Make_set(Dense_key)
