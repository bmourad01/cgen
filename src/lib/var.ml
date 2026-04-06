open Core
open Regular.Std

type t = Int63.t [@@deriving bin_io, compare, equal, hash, sexp]

module Tree = Patricia_tree.Make(struct
    include Int63
    let size = 63
    let to_int = to_int_trunc
  end)

module Tree_set = Patricia_tree.Make_set(struct
    include Int63
    let size = 63
    let to_int = to_int_trunc
  end)

include Regular.Make(struct
    type nonrec t = t [@@deriving bin_io, compare, equal, hash, sexp]
    let pp ppf v = Format.fprintf ppf "%%%a" Int63.pp v
    let version = "0.1"
    let module_name = Some "Cgen.Var"
  end)
