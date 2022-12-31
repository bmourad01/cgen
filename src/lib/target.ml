open Core

type t = {
  name : string;
} [@@deriving bin_io, compare, equal, hash, sexp]
