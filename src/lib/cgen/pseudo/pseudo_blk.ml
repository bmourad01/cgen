open Core
open Pseudo_common
open Cgen_containers

type 'a t = {
  label : Label.t;
  insns : 'a Pseudo_insn.t ftree;
} [@@deriving bin_io, compare, equal, sexp]

let create ~label ~insns = {
  label;
  insns = Ftree.of_list insns
}

let label t = t.label
let has_label t l = Label.equal l t.label
let insns ?(rev = false) t = Ftree.enum ~rev t.insns

let has_any_insns t = not (Ftree.is_empty t.insns)
let num_insns t = Ftree.length t.insns

let fold_insns ?(rev = false) t ~init ~f =
  if rev then Ftree.fold_right t.insns ~init ~f:(fun x acc -> f acc x)
  else Ftree.fold t.insns ~init ~f

let iter_insns ?(rev = false) t ~f =
  if rev then Ftree.iter_rev t.insns ~f
  else Ftree.iter t.insns ~f

let map_insns t ~f = {
  t with insns = Ftree.map t.insns ~f;
}

let with_insns t is = {
  t with insns = Ftree.of_list is;
}

let pp ppa ppf t =
  let sep ppf = Format.fprintf ppf "@;" in
  match Ftree.is_empty t.insns with
  | true ->
    Format.fprintf ppf "%a:" Label.pp t.label
  | false ->
    Format.fprintf ppf "%a:@;@[<v 2>  %a@]"
      Label.pp t.label
      (Ftree.pp (Pseudo_insn.pp ppa) sep) t.insns
