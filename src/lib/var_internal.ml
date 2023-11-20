open Core

type id = Int63.t [@@deriving bin_io, compare, equal, hash, sexp]

type t =
  | Temp of id * int
  | Name of string * int
[@@deriving bin_io, compare, equal, hash, sexp]

let temp ?(index = 0) id = Temp (id, index)
