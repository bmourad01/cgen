open Core
open Regular.Std

module Slot = Virtual.Slot
module Vset = Var.Tree_set

let (@/) i s = not @@ Set.mem s i
let (--) = Vset.remove
let (++) = Vset.union
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
    val free_vars : t -> Vset.t
  end

  module Ctrl : sig
    type t
    type table
    val free_vars : t -> Vset.t
  end

  module Blk : sig
    type t
    val label : t -> Label.t
    val ctrl : t -> Ctrl.t
    val dict : t -> Dict.t
    val has_any_args : t -> bool
    val args_to_list : t -> Var.t list
    val num_args : t -> int
    val fold_args : ?rev:bool -> t -> init:'a -> f:('a -> Var.t -> 'a) -> 'a
    val fold_insns : ?rev:bool -> t -> init:'a -> f:('a -> Insn.t -> 'a) -> 'a

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
    val fold_slots : ?rev:bool -> t -> init:'a -> f:('a -> Slot.t -> 'a) -> 'a
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
    val ins : t -> Label.t -> Vset.t
    val outs : t -> Label.t -> Vset.t
    val uses : t -> Label.t -> Vset.t
    val compute' : ?keep:Vset.t -> Cfg.t -> Blk.t Label.Tree.t -> t
  end

  val map_ctrl : unused -> Ctrl.t -> Ctrl.t * bool
end

module Make(M : S) = struct
  open M

  let collect_unused_args live blks : unused =
    Label.Tree.fold blks ~init:Label.Tree.empty
      ~f:(fun ~key:_ ~data:b acc ->
          if not (Blk.has_any_args b) then acc else
            let l = Blk.label b in
            let needed = Live.uses live l ++ Live.outs live l in
            let args =
              Blk.fold_args b
                ~init:(0, Int.Set.empty)
                ~f:(fun (i, acc) x ->
                    let acc =
                      if Vset.mem needed x then acc
                      else Set.add acc i in
                    i + 1, acc) |> snd in
            if Set.is_empty args then acc
            else Label.Tree.set acc ~key:l ~data:args)

  let keep i x alive =
    Insn.is_effectful i ||
    Vset.mem alive x ||
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
    Func.fold_slots fn ~init:fn ~f:(fun acc s ->
        let x = Slot.var s in
        if Vset.mem ins x then acc else remove_slot acc x) |>
    Fn.flip Func.update_blks' blks

  let filter_args b s =
    Blk.fold_args ~rev:true b
      ~init:(Blk.num_args b - 1, [])
      ~f:(fun (i, acc) a ->
          let acc = if i @/ s then a :: acc else acc in
          i - 1, acc) |> snd

  let rec run fn blks cfg =
    let live = Live.compute' cfg blks in
    let unused = collect_unused_args live blks in
    Label.Tree.fold blks ~init:[] ~f:(fun ~key:label ~data:b acc ->
        let ctrl, cc = map_ctrl unused @@ Blk.ctrl b in
        let unused_s = Label.Tree.find unused label in
        let ca = Option.is_some unused_s in
        let alive = Live.outs live label ++ Ctrl.free_vars ctrl in
        let insns, changed, _ =
          Blk.fold_insns b ~rev:true ~init:([], ca || cc, alive) ~f:insn in
        if changed then
          let args = match unused_s with
            | Some s -> filter_args b s
            | None -> Blk.args_to_list b in
          Blk.create () ~insns ~ctrl ~label ~args ~dict:(Blk.dict b) :: acc
        else acc) |> function
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
