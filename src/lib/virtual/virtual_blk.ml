open Core
open Regular.Std
open Virtual_common

module Insn = Virtual_insn
module Ctrl = Virtual_ctrl

module T = struct
  type t = {
    label : Label.t;
    args  : Var.t ftree;
    insns : Insn.t ftree;
    ctrl  : Ctrl.t;
    dict  : Dict.t;
  } [@@deriving bin_io, compare, equal, sexp]
end

include T

let create
    ?(dict = Dict.empty)
    ?(args = [])
    ?(insns = [])
    ~label ~ctrl () = {
  label;
  args = Ftree.of_list args;
  insns = Ftree.of_list insns;
  ctrl;
  dict;
}

let label b = b.label
let args ?(rev = false) b = Ftree.enum b.args ~rev
let insns ?(rev = false) b = Ftree.enum b.insns ~rev
let ctrl b = b.ctrl
let has_label b l = Label.(b.label = l)
let hash b = Label.hash b.label
let dict b = b.dict
let with_dict b dict = {b with dict}
let with_tag b tag x = {b with dict = Dict.set b.dict tag x}

let map_of_insns b =
  Ftree.fold b.insns ~init:Label.Tree.empty ~f:(fun m d ->
      let key = Insn.label d in
      match Label.Tree.add m ~key ~data:d with
      | `Ok m -> m
      | `Duplicate ->
        invalid_argf
          "Duplicate block of label %a in block %a"
          Label.pps key Label.pps b.label ())

let free_vars b =
  let (++) = Set.union and (--) = Set.diff in
  let def i = match Insn.lhs i with
    | Some x -> Var.Set.singleton x
    | None -> Var.Set.empty in
  let init = Ctrl.free_vars b.ctrl in
  Ftree.fold_right b.insns ~init ~f:(fun i inc ->
      inc -- def i ++ Insn.free_vars i)

let uses_var b x = Set.mem (free_vars b) x

let map_args b ~f = {
  b with args = Ftree.map b.args ~f:(fun x -> f x);
}

let map_insns b ~f = {
  b with insns = Ftree.map b.insns ~f:(fun d ->
    Insn.map d ~f:(f d.label));
}

let map_ctrl b ~f = {
  b with ctrl = f b.ctrl;
}

let prepend_arg ?before b a = {
  b with args = Ftree.icons ?before b.args a Var.equal;
}

let append_arg ?after b a = {
  b with args = Ftree.isnoc ?after b.args a Var.equal;
}

let prepend_insn ?before b d = {
  b with insns = Ftree.icons ?before b.insns d Insn.has_label;
}

let append_insn ?after b d = {
  b with insns = Ftree.isnoc ?after b.insns d Insn.has_label;
}

let prepend_insns ?before b ds = {
  b with insns = Ftree.icons_multi ?before b.insns ds Insn.has_label;
}

let append_insns ?after b ds = {
  b with insns = Ftree.isnoc_multi ?after b.insns ds Insn.has_label;
}

let with_ctrl b c = {
  b with ctrl = c;
}

let with_insns b is = {
  b with insns = Ftree.of_list is;
}

let with_args b args = {
  b with args = Ftree.of_list args;
}

let remove_arg b x = {
  b with args = Ftree.remove_if b.args ~f:(Var.equal x);
}

let remove_insn b l = {
  b with insns = Ftree.remove_if b.insns ~f:(Fn.flip Insn.has_label l);
}

let has_arg b x = Ftree.exists b.args ~f:(Var.equal x)
let has_lhs b x = Ftree.exists b.insns ~f:(fun i -> Insn.(has_lhs i) x)
let defines_var b x = has_arg b x || has_lhs b x
let has_insn b l = Ftree.exists b.insns ~f:(Fn.flip Insn.has_label l)
let find_insn b l = Ftree.find b.insns ~f:(Fn.flip Insn.has_label l)
let next_insn b l = Ftree.next b.insns ~f:(Fn.flip Insn.has_label l)
let prev_insn b l = Ftree.prev b.insns ~f:(Fn.flip Insn.has_label l)

let pp_args ppf args =
  let sep ppf = Format.fprintf ppf ", " in
  if not @@ Ftree.is_empty args then
    Format.fprintf ppf "(%a)"
      (Ftree.pp Var.pp sep) args

let pp ppf b =
  let sep ppf = Format.fprintf ppf "@;" in
  match Ftree.is_empty b.insns with
  | true ->
    Format.fprintf ppf "%a%a:@;  %a"
      Label.pp b.label
      pp_args b.args
      Ctrl.pp b.ctrl
  | false ->
    Format.fprintf ppf "%a%a:@;@[<v 2>  %a@;%a@]"
      Label.pp b.label
      pp_args b.args
      (Ftree.pp Insn.pp sep) b.insns
      Ctrl.pp b.ctrl

include Regular.Make(struct
    include T
    let module_name = Some "Cgen.Virtual.Blk"
    let version = "0.1"
    let pp = pp
    let hash = hash
  end)
