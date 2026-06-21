open Core
open Regular.Std

module Slot = Virtual.Slot
module Vset = Var.Tree_set
module VS = Var.Dense_set
module VT = Var.Dense_table
module LT = Label.Dense_table

let (@/) i s = not @@ Set.mem s i
let noti s i _ = i @/ s

type unused = Int.Set.t Label.Tree.t

module type S = sig
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
    val roots : t -> Vset.t
    val locals : t -> (Label.t * Var.t option list) list
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
    val fold_slots : ?rev:bool -> t -> init:'a -> f:('a -> Slot.t -> 'a) -> 'a
    val remove_slot : t -> Var.t -> t
    val update_blks' : t -> Blk.t Label.Tree.t -> t
    val map_of_blks : t -> Blk.t Label.Tree.t
    val num_insns : t -> int
  end

  val map_ctrl : unused -> Ctrl.t -> Ctrl.t * bool
end

module Make(M : S) = struct
  open M

  let mark blks ~capacity =
    let idef = VT.create ~capacity () in
    let pdef = VT.create () in
    let feeds = LT.create () in
    let live = VS.create ~capacity () in
    let work = Stack.create () in
    let push x = if VS.strict_add live x then Stack.push work x in
    Label.Tree.iter blks ~f:(fun ~key:l ~data:b ->
        let _  = Blk.fold_args b ~init:0 ~f:(fun i x ->
            VT.set pdef ~key:x ~data:(l, i);
            i + 1) in
        Blk.fold_insns b ~init:() ~f:(fun () i ->
            if Insn.is_effectful i || Insn.check_div_rem i
            then Vset.iter (Insn.free_vars i) ~f:push
            else match Insn.lhs i with
              | Some x -> VT.set idef ~key:x ~data:i
              | None -> ());
        let c = Blk.ctrl b in
        Vset.iter (Ctrl.roots c) ~f:push;
        Ctrl.locals c |> List.iter ~f:(fun (tl, args) ->
            LT.update feeds tl ~f:(function
                | None -> [args]
                | Some xs -> args :: xs)));
    Stack.until_empty work (fun v ->
        match VT.find idef v with
        | Some i -> Vset.iter (Insn.free_vars i) ~f:push
        | None -> match VT.find pdef v with
          | None -> ()
          | Some (l, pos) ->
            Option.iter (LT.find feeds l)
              ~f:(List.iter ~f:(fun args ->
                  match List.nth args pos with
                  | Some (Some u) -> push u
                  | _ -> ())));
    live

  let keep live i = match Insn.lhs i with
    | Some x -> Insn.is_effectful i || VS.mem live x || Insn.check_div_rem i
    | None -> true

  let collect_unused live blks : unused =
    Label.Tree.fold blks ~init:Label.Tree.empty
      ~f:(fun ~key:_ ~data:b acc ->
          if not (Blk.has_any_args b) then acc else
            let s = Blk.fold_args b ~init:(0, Int.Set.empty)
                ~f:(fun (i, acc) x ->
                    let acc = if VS.mem live x then acc else Set.add acc i in
                    i + 1, acc) |> snd in
            if Set.is_empty s then acc
            else Label.Tree.set acc ~key:(Blk.label b) ~data:s)

  let filter_args b s =
    Blk.fold_args ~rev:true b
      ~init:(Blk.num_args b - 1, [])
      ~f:(fun (i, acc) a ->
          let acc = if i @/ s then a :: acc else acc in
          i - 1, acc) |> snd

  let sweep live unused blks =
    Label.Tree.fold blks ~init:blks ~f:(fun ~key:label ~data:b acc ->
        let ctrl, cc = map_ctrl unused (Blk.ctrl b) in
        let unused_s = Label.Tree.find unused label in
        let insns, removed =
          Blk.fold_insns b
            ~rev:true
            ~init:([], false)
            ~f:(fun (acc, rm) i ->
                if keep live i then i :: acc, rm else
                  let () = Logs.debug (fun m ->
                      m "%s: %a is dead%!" __FUNCTION__
                        Label.pp (Insn.label i)) in
                  acc, true) in
        if cc || Option.is_some unused_s || removed then
          let args = match unused_s with
            | Some s -> filter_args b s
            | None -> Blk.args_to_list b in
          let data = Blk.create () ~insns ~ctrl ~label ~args ~dict:(Blk.dict b) in
          Label.Tree.set acc ~key:label ~data
        else acc)

  let remove_slot fn x =
    Logs.debug (fun m -> m "%s: slot %a is dead%!" __FUNCTION__ Var.pp x);
    Func.remove_slot fn x

  let finalize fn live blks =
    Func.fold_slots fn ~init:fn ~f:(fun acc s ->
        let x = Slot.var s in
        if VS.mem live x then acc else remove_slot acc x) |>
    Fn.flip Func.update_blks' blks

  let run fn =
    let blks = Func.map_of_blks fn in
    let live = mark blks ~capacity:(Func.num_insns fn) in
    let unused = collect_unused live blks in
    let blks = sweep live unused blks in
    finalize fn live blks
end
