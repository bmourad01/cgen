open Core
open Regular.Std

module Slot = Virtual.Slot

let (@/) i s = not @@ Set.mem s i
let (--) = Set.remove
let (++) = Set.union
let noti s i _ = i @/ s

type unused = Int.Set.t Label.Tree.t

module type S = sig
  type local
  type dst

  module Insn : sig
    type t
    val label : t -> Label.t
    val check_div_rem : t -> bool
    val is_effectful : t -> bool
    val lhs : t -> Var.t option
    val free_vars : t -> Var.Set.t
  end

  module Ctrl : sig
    type t
    type table
    val free_vars : t -> Var.Set.t
  end

  module Blk : sig
    type t
    val args : ?rev:bool -> t -> Var.t seq
    val insns : ?rev:bool -> t -> Insn.t seq
    val label : t -> Label.t
    val ctrl : t -> Ctrl.t
    val dict : t -> Dict.t

    val create :
      ?dict:Dict.t ->
      ?args:Var.t list ->
      ?insns:Insn.t list ->
      label:Label.t ->
      ctrl:Ctrl.t ->
      unit ->
      t
  end

  module Func : sig
    type t
    val entry : t -> Label.t
    val blks : ?rev:bool -> t -> Blk.t seq
    val slots : ?rev:bool -> t -> Slot.t seq
    val remove_slot : t -> Var.t -> t
    val update_blks' : t -> Blk.t Label.Tree.t -> t
    val map_of_blks : t -> Blk.t Label.Tree.t
  end

  module Cfg : sig
    include Label.Graph_s
    val create : Func.t -> t
  end

  module Live : sig
    type t
    val ins : t -> Label.t -> Var.Set.t
    val outs : t -> Label.t -> Var.Set.t
    val uses : t -> Label.t -> Var.Set.t
    val compute' : ?keep:Var.Set.t -> Cfg.t -> Blk.t Label.Tree.t -> t
  end

  val map_ctrl : unused -> Ctrl.t -> Ctrl.t * bool
end

module Make(M : S) = struct
  open M

  let collect_unused_args live blks : unused =
    Label.Tree.fold blks ~init:Label.Tree.empty
      ~f:(fun ~key:_ ~data:b acc ->
          let l = Blk.label b in
          let needed = Live.uses live l ++ Live.outs live l in
          let args =
            Blk.args b |> Seq.filter_mapi ~f:(fun i x ->
                Option.some_if (x @/ needed) i) |>
            Int.Set.of_sequence in
          if Set.is_empty args then acc
          else Label.Tree.set acc ~key:l ~data:args)

  let keep i x alive =
    Insn.is_effectful i ||
    Set.mem alive x ||
    Insn.check_div_rem i

  (* Note that we don't always kill defined variables here. If the
     function is in SSA form then keeping in them in the alive set
     shouldn't affect the results. *)
  let insn (acc, changed, alive) i = match Insn.lhs i with
    | Some x when not @@ keep i x alive ->
      Logs.debug (fun m ->
          m "%s: %a: %a is dead%!" __FUNCTION__
            Label.pp (Insn.label i) Var.pp x);
      acc, true, alive
    | Some x -> i :: acc, changed, alive -- x ++ Insn.free_vars i
    | None -> i :: acc, changed, alive ++ Insn.free_vars i

  let remove_slot fn x =
    Logs.debug (fun m -> m "%s: slot %a is dead%!" __FUNCTION__ Var.pp x);
    Func.remove_slot fn x

  let finalize fn blks live =
    let ins = Live.ins live @@ Func.entry fn in
    Func.slots fn |> Seq.map ~f:Slot.var |>
    Seq.filter ~f:(Fn.non @@ Set.mem ins) |>
    Seq.fold ~init:fn ~f:remove_slot |>
    Fn.flip Func.update_blks' blks

  let rec run fn blks cfg =
    let live = Live.compute' cfg blks in
    let unused = collect_unused_args live blks in
    Label.Tree.to_sequence blks |>
    Seq.filter_map ~f:(fun (label, b) ->
        let ctrl, cc = map_ctrl unused @@ Blk.ctrl b in
        let args = Blk.args b in
        let args, ca = match Label.Tree.find unused label with
          | Some s -> Seq.filteri args ~f:(noti s), true
          | None -> args, false in
        let alive = Live.outs live label ++ Ctrl.free_vars ctrl in
        let insns, changed, _ =
          Blk.insns b ~rev:true |>
          Seq.fold ~init:([], ca || cc, alive) ~f:insn in
        if changed then
          Option.some @@ Blk.create () ~insns ~ctrl ~label
            ~args:(Seq.to_list args) ~dict:(Blk.dict b)
        else None) |> Seq.to_list |> function
    | [] -> finalize fn blks live
    | bs ->
      let blks = List.fold bs ~init:blks ~f:(fun acc b ->
          Label.Tree.set acc ~key:(Blk.label b) ~data:b) in
      run fn blks cfg

  let run fn =
    let cfg = Cfg.create fn in
    let blks = Func.map_of_blks fn in
    run fn blks cfg
end
