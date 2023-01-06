open Core

type t = {
  name : string;
  bits : int;
} [@@deriving bin_io, compare, equal, hash, sexp]
