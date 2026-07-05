open Core
open Cgen_containers

module Regular = Cgen_utils.Regular
module Insn = Virtual_insn
module Ctrl = Virtual_ctrl

module T = struct
  type t = {
    label : Label.t;
    args  : Var.t Rrb.t;
    insns : Insn.t Rrb.t;
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
  args = Rrb.of_list args;
  insns = Rrb.of_list insns;
  ctrl;
  dict;
}

let label b = b.label

let args ?(rev = false) b =
  if rev then Rrb.to_sequence_rev b.args else Rrb.to_sequence b.args

let insns ?(rev = false) b =
  if rev then Rrb.to_sequence_rev b.insns else Rrb.to_sequence b.insns

let ctrl b = b.ctrl
let has_label b l = Label.(b.label = l)
let hash b = Label.hash b.label
let dict b = b.dict
let with_dict b dict = {b with dict}
let with_tag b tag x = {b with dict = Dict.set b.dict tag x}

let map_of_insns b =
  Rrb.fold b.insns ~init:Label.Tree.empty ~f:(fun m d ->
      let key = Insn.label d in
      match Label.Tree.add m ~key ~data:d with
      | `Ok m -> m
      | `Duplicate ->
        invalid_argf
          "Duplicate block of label %a in block %a"
          Label.pps key Label.pps b.label ())

let free_vars b =
  let (++) = Var.Tree_set.union and (--) = Var.Tree_set.diff in
  let def i = match Insn.lhs i with
    | Some x -> Var.Tree_set.singleton x
    | None -> Var.Tree_set.empty in
  let init = Ctrl.free_vars b.ctrl in
  Rrb.fold_right b.insns ~init ~f:(fun i inc ->
      inc -- def i ++ Insn.free_vars i)

let uses_var b x = Var.Tree_set.mem (free_vars b) x

let map_args b ~f = {
  b with args = Rrb.map b.args ~f:(fun x -> f x);
}

let map_insns b ~f = {
  b with insns = Rrb.map b.insns ~f:(fun d -> Insn.map d ~f:(f d.label));
}

let filter_insns b ~f = {b with insns = Rrb.filter b.insns ~f}

let map_ctrl b ~f = {
  b with ctrl = f b.ctrl;
}

let prepend_arg ?before b a =
  let args = match before with
    | None -> Rrb.cons a b.args
    | Some k -> Rrb.insert_before b.args (Rrb.singleton a) ~f:(fun x -> Var.equal x k) in
  {b with args}

let append_arg ?after b a =
  let args = match after with
    | None -> Rrb.snoc b.args a
    | Some k -> Rrb.insert_after b.args (Rrb.singleton a) ~f:(fun x -> Var.equal x k) in
  {b with args}

let prepend_insn ?before b d =
  let insns = match before with
    | None -> Rrb.cons d b.insns
    | Some k -> Rrb.insert_before b.insns (Rrb.singleton d) ~f:(fun i -> Insn.has_label i k) in
  {b with insns}

let append_insn ?after b d =
  let insns = match after with
    | None -> Rrb.snoc b.insns d
    | Some k -> Rrb.insert_after b.insns (Rrb.singleton d) ~f:(fun i -> Insn.has_label i k) in
  {b with insns}

let prepend_insns ?before b ds =
  let insns = match before with
    | None -> Rrb.append (Rrb.of_list ds) b.insns
    | Some k -> Rrb.insert_before b.insns (Rrb.of_list ds) ~f:(fun i -> Insn.has_label i k) in
  {b with insns}

let append_insns ?after b ds =
  let insns = match after with
    | None -> Rrb.append b.insns (Rrb.of_list ds)
    | Some k -> Rrb.insert_after b.insns (Rrb.of_list ds) ~f:(fun i -> Insn.has_label i k) in
  {b with insns}

let with_ctrl b c = {
  b with ctrl = c;
}

let with_insns b is = {
  b with insns = Rrb.of_list is;
}

let with_args b args = {
  b with args = Rrb.of_list args;
}

let remove_arg b x = {
  b with args = Rrb.filter b.args ~f:(Fn.non @@ Var.equal x);
}

let remove_insn b l = {
  b with insns = Rrb.filter b.insns ~f:(fun i -> not @@ Insn.has_label i l);
}

let has_arg b x = Rrb.exists b.args ~f:(Var.equal x)
let has_lhs b x = Rrb.exists b.insns ~f:(fun i -> Insn.(has_lhs i) x)
let has_any_insns b = not (Rrb.is_empty b.insns)
let has_any_args b = not (Rrb.is_empty b.args)
let num_insns b = Rrb.length b.insns
let num_args b = Rrb.length b.args

let fold_insns ?(rev = false) b ~init ~f =
  if rev then Rrb.fold_right b.insns ~init ~f:(fun x acc -> f acc x)
  else Rrb.fold b.insns ~init ~f

let iter_insns ?(rev = false) b ~f =
  if rev then Rrb.iter_rev b.insns ~f
  else Rrb.iter b.insns ~f

let fold_args ?(rev = false) b ~init ~f =
  if rev then Rrb.fold_right b.args ~init ~f:(fun x acc -> f acc x)
  else Rrb.fold b.args ~init ~f

let iter_args ?(rev = false) b ~f =
  if rev then Rrb.iter_rev b.args ~f
  else Rrb.iter b.args ~f

let args_to_list b = Rrb.to_list b.args
let defines_var b x = has_arg b x || has_lhs b x
let has_insn b l = Rrb.exists b.insns ~f:(fun i -> Insn.has_label i l)
let find_insn b l = Rrb.find b.insns ~f:(fun i -> Insn.has_label i l)

let next_insn b l =
  match Rrb.find_index b.insns ~f:(fun i -> Insn.has_label i l) with
  | Some i -> Rrb.get b.insns (i + 1)
  | None -> None

let prev_insn b l =
  match Rrb.find_index b.insns ~f:(fun i -> Insn.has_label i l) with
  | Some i when i > 0 -> Some (Rrb.get_exn b.insns (i - 1))
  | Some _ | None -> None

let pp_args ppf args =
  if not @@ Rrb.is_empty args then begin
    Format.fprintf ppf "(";
    let first = ref true in
    Rrb.iter args ~f:(fun a ->
        if !first then first := false else Format.fprintf ppf ", ";
        Var.pp ppf a);
    Format.fprintf ppf ")"
  end

let pp ppf b =
  let pp_insns ppf insns =
    let first = ref true in
    Rrb.iter insns ~f:(fun i ->
        if !first then first := false else Format.fprintf ppf "@;";
        Insn.pp ppf i) in
  match Rrb.is_empty b.insns with
  | true ->
    Format.fprintf ppf "%a%a:@;  %a"
      Label.pp b.label
      pp_args b.args
      Ctrl.pp b.ctrl
  | false ->
    Format.fprintf ppf "%a%a:@;@[<v 2>  %a@;%a@]"
      Label.pp b.label
      pp_args b.args
      pp_insns b.insns
      Ctrl.pp b.ctrl

include Regular.Make(struct
    include T
    let pp = pp
    let hash = hash
  end)
