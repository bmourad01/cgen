open Core
open Graphlib.Std
open Regular.Std
open Common

type tran = {
  defs : Var.Set.t;
  uses : Var.Set.t;
}

let empty_tran = {
  defs = Var.Set.empty;
  uses = Var.Set.empty;
}

type t = {
  blks : tran Label.Map.t;
  outs : (Label.t, Var.Set.t) Solution.t;
}

let pp_vars ppf vars =
  Format.pp_print_list
    ~pp_sep:Format.pp_print_space
    Var.pp ppf (Set.to_list vars)

let pp_transfer ppf {uses; defs} =
  Format.fprintf ppf "(%a) / (%a)" pp_vars uses pp_vars defs

let blk_defs b =
  Blk.data b |> Seq.filter_map ~f:Insn.lhs_of_data |>
  Seq.fold ~init:Var.Set.empty ~f:Set.add

let update l trans ~f = Map.update trans l ~f:(function
    | None -> f empty_tran
    | Some had -> f had)

let (++) = Set.union and (--) = Set.diff

let find_blk fn l = Func.blks fn |> Seq.find ~f:(Fn.flip Blk.has_label l)

let local_uses : local -> Var.Set.t = function
  | `label (l, args) ->
    List.filter_map args ~f:(function
        | `var v -> Some v | _ -> None) |>
    Var.Set.of_list

let dst_uses : dst -> Var.Set.t = function
  | #local as l -> local_uses l
  | _ -> Var.Set.empty

let ctrl_uses b = match Blk.ctrl b with
  | `hlt | `ret _ -> Var.Set.empty
  | `jmp d -> dst_uses d
  | `br (_, t, f) -> dst_uses t ++ dst_uses f
  | `sw (_, _, d, tbl) ->
    let init = local_uses d in
    Insn.Ctrl.Table.enum tbl |> Seq.map ~f:snd |>
    Seq.fold ~init ~f:(fun uses e -> uses ++ local_uses e)

let block_transitions g fn =
  Func.blks fn |> Seq.fold ~init:Label.Map.empty ~f:(fun fs b ->
      Map.add_exn fs ~key:(Blk.label b) ~data:{
        defs = blk_defs b;
        uses = Blk.free_vars b;
      }) |> fun init ->
  Func.blks fn |> Seq.fold ~init ~f:(fun init b ->
      let args =
        Blk.args b |> Seq.map ~f:fst |>
        Seq.fold ~init:Var.Set.empty ~f:Set.add in
      Cfg.Node.preds (Blk.label b) g |>
      Seq.fold ~init ~f:(fun fs p ->
          match find_blk fn p with
          | None -> fs
          | Some pb -> update p fs ~f:(fun {defs; uses} -> {
                defs = Set.union defs args;
                uses = uses ++ (ctrl_uses pb -- defs);
              })))

let lookup blks n = Map.find blks n |> Option.value ~default:empty_tran
let apply {defs; uses} vars = vars -- defs ++ uses

let transfer blks n vars =
  if Label.is_pseudo n then vars else apply (lookup blks n) vars

let compute ?(keep = Var.Set.empty) fn =
  let g = Cfg.create fn in
  let init =
    Solution.create
      (Label.Map.singleton Label.pseudoexit keep)
      Var.Set.empty in
  let blks = block_transitions g fn in {
    blks;
    outs = Graphlib.fixpoint (module Cfg) g ~init
        ~rev:true ~start:Label.pseudoexit
        ~merge:Set.union ~equal:Var.Set.equal
        ~f:(transfer blks);
  }

let outs t l = Solution.get t.outs l
let ins  t l = transfer t.blks l @@ outs t l
let defs t l = (lookup t.blks l).defs
let uses t l = (lookup t.blks l).uses

let fold t ~init ~f =
  Map.fold t.blks ~init ~f:(fun ~key:l ~data:trans init ->
      f init l @@ apply trans @@ outs t l)

let blks t x = fold t ~init:Label.Set.empty ~f:(fun blks l ins ->
    if Set.mem ins x then Set.add blks l else blks)

let solution t = t.outs

let pp ppf t =
  Format.pp_open_vbox ppf 0;
  fold t ~init:() ~f:(fun () l vars ->
      Format.fprintf ppf "@[<h>%a: @[<hov 2>(%a)@]@]@;"
        Label.pp l pp_vars vars);
  Format.pp_close_box ppf ()
