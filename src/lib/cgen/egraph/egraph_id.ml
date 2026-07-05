open Core
open Cgen_containers

type t = int [@@deriving bin_io, equal, compare, hash, sexp]

let pp = Int.pp
let to_string = Int.to_string

module Key = struct
  include Int
  let size = Sys.int_size_in_bits
end

module Set = Int.Set
module Tree_set = Patricia_tree.Make_set(Key)
