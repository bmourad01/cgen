open Core

type 'a t = {
  label : Label.t;
  insn  : 'a;
} [@@deriving bin_io, compare, equal, sexp]

let create ~label ~insn = {label; insn}

let label t = t.label
let insn t = t.insn
let with_insn t i = {t with insn = i}

let pp ppa ppf i =
  Format.fprintf ppf "%a ; %a" ppa i.insn Label.pp i.label
