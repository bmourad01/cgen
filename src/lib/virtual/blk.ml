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
    args  : (Var.t * arg_typ) array;
    insns : Insn.t array;
    ctrl  : Ctrl.t;
  } [@@deriving bin_io, compare, equal, sexp]
end

include T

let create ?(args = []) ?(insns = []) ~label ~ctrl () = try {
  label;
  args = Array.of_list args;
  insns = Array.of_list insns;
  ctrl;
} with exn -> invalid_argf "%s" (Exn.to_string exn) ()

let label b = b.label
let args ?(rev = false) b = Array.enum b.args ~rev
let insns ?(rev = false) b = Array.enum b.insns ~rev
let ctrl b = b.ctrl
let has_label b l = Label.(b.label = l)
let hash b = Label.hash b.label

let map_of_insns b =
  Array.fold b.insns ~init:Label.Map.empty ~f:(fun m d ->
      let key = Insn.label d in
      match Map.add m ~key ~data:d with
      | `Ok m -> m
      | `Duplicate ->
        invalid_argf
          "Duplicate block of label %a in block %a"
          Label.pps key Label.pps b.label ())

let free_vars b =
  let (++) = Set.union and (--) = Set.diff in
  let init = Var.Set.(empty, empty) in
  let vars, kill = Array.fold b.insns ~init ~f:(fun (vars, kill) d ->
      let kill' = match Insn.lhs d with
        | Some x -> Set.add kill x
        | None -> kill in
      Insn.free_vars d -- kill ++ vars, kill') in
  Ctrl.free_vars b.ctrl -- kill ++ vars

let uses_var b x = Set.mem (free_vars b) x

let map_args b ~f = {
  b with args = Array.map b.args ~f:(fun (x, t) -> f x t);
}

let map_insns b ~f = {
  b with insns = Array.map b.insns ~f:(fun d ->
    Insn.map d ~f:(f d.label));
}

let map_ctrl b ~f = {
  b with ctrl = f b.ctrl;
}

let index_of xs f i =
  Array.findi xs ~f:(fun _ x -> f x i) |> Option.map ~f:fst

let prepend ?(before = None) xs x f = match before with
  | None -> Array.push_front xs x
  | Some i -> index_of xs f i |> function
    | Some i -> Array.insert xs x i
    | None -> xs

let append ?(after = None) xs x f = match after with
  | None -> Array.push_back xs x
  | Some i -> index_of xs f i |> function
    | Some i -> Array.insert xs x (i + 1)
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

let remove xs i f = Array.remove_if xs ~f:(Fn.flip f i)
let remove_arg b x = {b with args = remove b.args x is_arg}
let remove_insn b l = {b with insns = remove b.insns l Insn.has_label}

let has_arg b x = Array.exists b.args ~f:(Fn.flip is_arg x)

let typeof_arg b x =
  Array.find b.args ~f:(Fn.flip is_arg x) |>
  Option.map ~f:snd

let has_lhs b x = Array.exists b.insns ~f:(fun i -> Insn.(has_lhs i) x)
let defines_var b x = has_arg b x || has_lhs b x

let has_insn b l = Array.exists b.insns ~f:(Fn.flip Insn.has_label l)
let find_insn b l = Array.find b.insns ~f:(Fn.flip Insn.has_label l)
let next_insn b l = Array.next b.insns Insn.label l
let prev_insn b l = Array.prev b.insns Insn.label l

let pp_arg ppf (x, t) =
  Format.fprintf ppf "%a %a" pp_arg_typ t Var.pp x

let pp_args ppf args =
  let sep ppf = Format.fprintf ppf ", " in
  if not @@ Array.is_empty args then
    Format.fprintf ppf "(%a)"
      (Array.pp pp_arg sep) args

let pp ppf b =
  let sep ppf = Format.fprintf ppf "@;" in
  match b.insns with
  | [||] ->
    Format.fprintf ppf "%a%a:@;  %a"
      Label.pp b.label
      pp_args b.args
      Ctrl.pp b.ctrl
  | insns ->
    Format.fprintf ppf "%a%a:@;@[<v 2>  %a@;%a@]"
      Label.pp b.label
      pp_args b.args
      (Array.pp Insn.pp sep)insns
      Ctrl.pp b.ctrl

include Regular.Make(struct
    include T
    let module_name = Some "Cgen.Virtual.Blk"
    let version = "0.1"
    let pp = pp
    let hash = hash
  end)
