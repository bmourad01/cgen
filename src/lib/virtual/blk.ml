open Core
open Regular.Std
open Common

type arg_typ = [
  | Type.basic
  | Type.special
] [@@deriving bin_io, compare, equal, sexp]

let pp_arg_typ ppf t =
  Format.fprintf ppf "%a" Type.pp (t :> Type.t)

module T = struct
  type t = {
    label : Label.t;
    args  : (Var.t * arg_typ) ftree;
    insns : Insn.t ftree;
    ctrl  : Ctrl.t;
  } [@@deriving bin_io, compare, equal, sexp]
end

include T

let create ?(args = []) ?(insns = []) ~label ~ctrl () = {
  label;
  args = Ftree.of_list args;
  insns = Ftree.of_list insns;
  ctrl;
}

let label b = b.label
let args ?(rev = false) b = Ftree.enum b.args ~rev
let insns ?(rev = false) b = Ftree.enum b.insns ~rev
let ctrl b = b.ctrl
let has_label b l = Label.(b.label = l)
let hash b = Label.hash b.label

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
  let init = Var.Set.(empty, empty) in
  let vars, kill = Ftree.fold b.insns ~init ~f:(fun (vars, kill) d ->
      let kill' = match Insn.lhs d with
        | Some x -> Set.add kill x
        | None -> kill in
      Insn.free_vars d -- kill ++ vars, kill') in
  Ctrl.free_vars b.ctrl -- kill ++ vars

let uses_var b x = Set.mem (free_vars b) x

let map_args b ~f = {
  b with args = Ftree.map b.args ~f:(fun (x, t) -> f x t);
}

let map_insns b ~f = {
  b with insns = Ftree.map b.insns ~f:(fun d ->
    Insn.map d ~f:(f d.label));
}

let map_ctrl b ~f = {
  b with ctrl = f b.ctrl;
}

let index_of xs f i =
  Ftree.findi xs ~f:(fun _ x -> f x i) |> Option.map ~f:fst

let prepend ?(before = None) xs x f = match before with
  | None -> Ftree.cons xs x
  | Some i -> index_of xs f i |> function
    | Some i -> Ftree.insert xs x i
    | None -> xs

let append ?(after = None) xs x f = match after with
  | None -> Ftree.snoc xs x
  | Some i -> index_of xs f i |> function
    | Some i -> Ftree.insert xs x (i + 1)
    | None -> xs

let is_arg (x, _) y = Var.(x = y)

let prepend_arg ?(before = None) b a = {
  b with args = prepend b.args a is_arg ~before;
}

let append_arg ?(after = None) b a = {
  b with args = append b.args a is_arg ~after;
}

let prepend_insn ?(before = None) b d = {
  b with insns = prepend b.insns d Insn.has_label ~before;
}

let append_insn ?(after = None) b d = {
  b with insns = append b.insns d Insn.has_label ~after;
}

let remove xs i f = Ftree.remove_if xs ~f:(Fn.flip f i)
let remove_arg b x = {b with args = remove b.args x is_arg}
let remove_insn b l = {b with insns = remove b.insns l Insn.has_label}

let has_arg b x = Ftree.exists b.args ~f:(Fn.flip is_arg x)

let typeof_arg b x =
  Ftree.find b.args ~f:(Fn.flip is_arg x) |>
  Option.map ~f:snd

let has_lhs b x = Ftree.exists b.insns ~f:(fun i -> Insn.(has_lhs i) x)
let defines_var b x = has_arg b x || has_lhs b x

let has_insn b l = Ftree.exists b.insns ~f:(Fn.flip Insn.has_label l)
let find_insn b l = Ftree.find b.insns ~f:(Fn.flip Insn.has_label l)
let next_insn b l = Ftree.next b.insns ~f:(Fn.flip Insn.has_label l)
let prev_insn b l = Ftree.prev b.insns ~f:(Fn.flip Insn.has_label l)

let pp_arg ppf (x, t) =
  Format.fprintf ppf "%a %a" pp_arg_typ t Var.pp x

let pp_args ppf args =
  let sep ppf = Format.fprintf ppf ", " in
  if not @@ Ftree.is_empty args then
    Format.fprintf ppf "(%a)"
      (Ftree.pp pp_arg sep) args

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
