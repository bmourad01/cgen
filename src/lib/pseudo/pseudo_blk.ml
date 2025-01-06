open Core
open Pseudo_common

type 'a t = {
  label : Label.t;
  insns : 'a ftree;
} [@@deriving bin_io, compare, equal, sexp]

let create ~label ~insns = {
  label;
  insns = Ftree.of_list insns
}

let label t = t.label
let insns ?(rev = false) t = Ftree.enum ~rev t.insns

let pp ppa ppf t =
  let sep ppf = Format.fprintf ppf "@;" in
  match Ftree.is_empty t.insns with
  | true ->
    Format.fprintf ppf "%a:" Label.pp t.label
  | false ->
    Format.fprintf ppf "%a:@;@[<v 2>  %a@]"
      Label.pp t.label
      (Ftree.pp ppa sep) t.insns
