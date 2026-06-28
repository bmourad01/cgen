open Core
open Cgen_containers

type 'a t = {
  label : Label.t;
  insns : 'a Pseudo_insn.t Rrb.t;
} [@@deriving bin_io, compare, equal, sexp]

let create ~label ~insns = {
  label;
  insns = Rrb.of_list insns
}

let label t = t.label
let has_label t l = Label.equal l t.label

let insns ?(rev = false) t =
  if rev then Rrb.to_sequence_rev t.insns else Rrb.to_sequence t.insns

let has_any_insns t = not (Rrb.is_empty t.insns)
let num_insns t = Rrb.length t.insns

let fold_insns ?(rev = false) t ~init ~f =
  if rev then Rrb.fold_right t.insns ~init ~f:(fun x acc -> f acc x)
  else Rrb.fold t.insns ~init ~f

let iter_insns ?(rev = false) t ~f =
  if rev then Rrb.iter_rev t.insns ~f
  else Rrb.iter t.insns ~f

let map_insns t ~f = {
  t with insns = Rrb.map t.insns ~f;
}

let filter_insns t ~f = {t with insns = Rrb.filter t.insns ~f}

let with_insns t is = {
  t with insns = Rrb.of_list is;
}

let pp ppa ppf t =
  let pp_insns ppf insns =
    let first = ref true in
    Rrb.iter insns ~f:(fun i ->
        if !first then first := false else Format.fprintf ppf "@;";
        Pseudo_insn.pp ppa ppf i) in
  match Rrb.is_empty t.insns with
  | true ->
    Format.fprintf ppf "%a:" Label.pp t.label
  | false ->
    Format.fprintf ppf "%a:@;@[<v 2>  %a@]"
      Label.pp t.label pp_insns t.insns
