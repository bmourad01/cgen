open Core
open Graphlib.Std
open Regular.Std

module type L = sig
  type lhs

  module Insn : sig
    type t
    type op
    val op : t -> op
    val label : t -> Label.t
    val has_label : t -> Label.t -> bool
    val with_op : t -> op -> t
    val lhs : t -> Var.t list
  end

  module Ctrl : sig
    type t
  end

  module Blk : sig
    type t

    val create :
      ?dict:Dict.t ->
      ?args:Var.t list ->
      ?insns:Insn.t list ->
      label:Label.t ->
      ctrl:Ctrl.t ->
      unit ->
      t

    val label : t -> Label.t
    val dict : t -> Dict.t
    val args : ?rev:bool -> t -> Var.t seq
    val insns : ?rev:bool -> t -> Insn.t seq
    val ctrl : t -> Ctrl.t
  end

  module Func : sig
    type t
    val dict : t -> Dict.t
    val with_tag : t -> 'a Dict.tag -> 'a -> t
    val name : t -> string
    val blks : ?rev:bool -> t -> Blk.t seq
    val update_blks_exn : t -> Blk.t list -> t
  end

  module Cfg : sig
    include Label.Graph
    val create : Func.t -> t
  end

  module Live : Live_intf.S with type func := Func.t

  module Resolver : Resolver_intf.S
    with type lhs := lhs
     and type insn := Insn.t
     and type blk := Blk.t
     and type func := Func.t

  val argify_ctrl : inc:(Label.t -> Var.t list) -> Ctrl.t -> Ctrl.t

  val rename_op :
    stk:(Var.t -> Var.t) ->
    rename:(Var.t -> Var.t) ->
    Insn.op ->
    Insn.op

  val rename_ctrl : stk:(Var.t -> Var.t) -> Ctrl.t -> Ctrl.t
end

module Make(M : L) = struct
  open M

  exception Missing_blk of Label.t

  type env = {
    live     : Live.t;
    cfg      : Cfg.t;
    dom      : Label.t tree;
    frontier : Label.t frontier;
    blks     : Blk.t Label.Table.t;
    stk      : Var.t list Var.Table.t;
    nums     : int Var.Table.t;
  }

  let init fn =
    let live = Live.compute fn in
    let cfg = Cfg.create fn in
    let dom = Graphlib.dominators (module Cfg) cfg Label.pseudoentry in
    let frontier = Graphlib.dom_frontier (module Cfg) cfg dom in
    let blks = Label.Table.create () in
    let stk = Var.Table.create () in
    let nums = Var.Table.create () in
    Func.blks fn |> Seq.iter ~f:(fun b ->
        Hashtbl.set blks ~key:(Blk.label b) ~data:b);
    {live; cfg; dom; frontier; blks; stk; nums}

  let find_blk env l = match Hashtbl.find env.blks l with
    | None when Label.is_pseudo l -> None
    | None -> raise @@ Missing_blk l
    | Some _ as b -> b

  (* First phase of the algorithm is to insert arguments to basic blocks
     and control-flow instructions based on the dominance frontier. *)
  module Phi : sig
    val go : env -> unit
  end = struct
    type state = {
      defs : Label.Set.t Var.Table.t;
      args : Var.t list Label.Table.t;
      ctrl : Ctrl.t Label.Table.t;
      outs : Var.t list Label.Tree.t Label.Table.t;
    }

    let define defs x l = Hashtbl.update defs x ~f:(function
        | None -> Label.Set.singleton l
        | Some s -> Set.add s l)

    let blocks_that_define_var st x =
      Hashtbl.find st.defs x |>
      Option.value ~default:Label.Set.empty

    let has_arg st l x =
      Hashtbl.find st.args l |>
      Option.value_map ~default:false ~f:(fun args ->
          List.mem args x ~equal:Var.equal)

    let init env =
      let defs = Var.Table.create () in
      let args = Label.Table.create () in
      let ctrl = Label.Table.create () in
      let outs = Label.Table.create () in
      Hashtbl.iteri env.blks ~f:(fun ~key:l ~data:b ->
          let args' = Seq.to_list @@ Blk.args b in
          Hashtbl.set args ~key:l ~data:args';
          List.iter args' ~f:(fun x -> define defs x l);
          Blk.insns b |> Seq.to_list |> List.concat_map ~f:Insn.lhs |>
          List.iter ~f:(fun x -> define defs x l);
          Hashtbl.set ctrl ~key:l ~data:(Blk.ctrl b));
      {defs; args; ctrl; outs}

    let update_incoming env l x outs =
      Cfg.Node.preds l env.cfg |> Seq.iter ~f:(fun l' ->
          Hashtbl.update outs l' ~f:(function
              | None -> Label.Tree.singleton l [x]
              | Some inc ->
                Label.Tree.update_with inc l
                  ~has:(List.cons x)
                  ~nil:(fun () -> [x])))

    let add_arg env st l x =
      Hashtbl.add_multi st.args ~key:l ~data:x;
      update_incoming env l x st.outs

    let iterated_frontier f blks =
      let blks = Set.add blks Label.pseudoentry in
      let df = Set.fold ~init:Label.Set.empty ~f:(fun init b ->
          Frontier.enum f b |> Seq.fold ~init ~f:Set.add) in
      let rec fixpoint idf =
        let idf' = df @@ Set.union idf blks in
        if Set.equal idf idf' then idf' else fixpoint idf' in
      fixpoint Label.Set.empty

    let needs_arg env st l x =
      Set.mem (Live.ins env.live l) x &&
      not (has_arg st l x)

    let insert_blk_args env st =
      Live.fold env.live ~init:Var.Set.empty
        ~f:(fun u _ v -> Set.union u v) |>
      Set.iter ~f:(fun x ->
          blocks_that_define_var st x |>
          iterated_frontier env.frontier |>
          Set.iter ~f:(fun l ->
              if needs_arg env st l x
              then add_arg env st l x))

    let find_inc inc l = Label.Tree.find inc l |> Option.value ~default:[]

    let insert_ctrl_args st =
      Hashtbl.iteri st.outs ~f:(fun ~key:l ~data:inc ->
          if not @@ Label.is_pseudo l then
            Hashtbl.update st.ctrl l ~f:(function
                | Some c -> argify_ctrl ~inc:(find_inc inc) c
                | None -> assert false))

    let go env =
      let st = init env in
      insert_blk_args env st;
      insert_ctrl_args st;
      Hashtbl.map_inplace env.blks ~f:(fun b ->
          let label = Blk.label b in
          let dict = Blk.dict b in
          let args = Hashtbl.find_exn st.args label in
          let ctrl = Hashtbl.find_exn st.ctrl label in
          let insns = Blk.insns b |> Seq.to_list in
          Blk.create ~dict ~args ~insns ~ctrl ~label ())
  end

  (* Second phase of the algorithm is to traverse the dominator tree
     and rename variables in each block according to their use-def
     chains. *)
  module Rename : sig
    val go : env -> unit
  end = struct
    let new_name env x =
      let key = Var.base x in
      let default = 1 in
      let n = ref default in
      let upd x = n := x + 1; !n in
      Hashtbl.update env.nums key ~f:(Option.value_map ~default ~f:upd);
      let y = Var.with_index x !n in
      Hashtbl.add_multi env.stk ~key ~data:y;
      y

    let rename_args env b =
      Blk.args b |> Seq.map ~f:(new_name env) |> Seq.to_list

    let map_var env x = match Hashtbl.find env.stk x with
      | Some [] | None -> x
      | Some (y :: _) -> y

    let rename_insns env b =
      let stk = map_var env in
      let rename = new_name env in
      Blk.insns b |> Seq.map ~f:(fun i ->
          Insn.op i |> rename_op ~stk ~rename |> Insn.with_op i) |>
      Seq.to_list

    let pop_defs env b =
      let pop x = Var.base x |> Hashtbl.change env.stk ~f:(function
          | Some ([] | [_]) | None -> None
          | Some (_ :: xs) -> Some xs) in
      Blk.args b |> Seq.iter ~f:pop;
      Blk.insns b |> Seq.to_list |>
      List.concat_map ~f:Insn.lhs |>
      List.iter ~f:pop

    type action =
      | Visit of Label.t
      | Pop of Blk.t

    let visit q env l =
      let b = find_blk env l in
      Option.iter b ~f:(fun b ->
          (* Rename the variables in the block. *)
          let dict = Blk.dict b in
          let args = rename_args env b in
          let insns = rename_insns env b in
          let ctrl = rename_ctrl ~stk:(map_var env) @@ Blk.ctrl b in
          let b' = Blk.create ~dict ~args ~insns ~ctrl ~label:l () in
          Hashtbl.set env.blks ~key:l ~data:b';
          (* Pop the renamed variables from the stack. *)
          Stack.push q @@ Pop b);
      (* Repeat for the children in the dominator tree. *)
      Tree.children env.dom l |> Seq.iter
        ~f:(fun l -> Stack.push q @@ Visit l)

    let go env =
      let q = Stack.singleton @@ Visit Label.pseudoentry in
      Stack.until_empty q @@ function
      | Visit l -> visit q env l
      | Pop b -> pop_defs env b
  end

  module Check : sig
    val go : Label.t tree -> Func.t -> unit
  end = struct
    let fail fn = failwithf "$%s violates SSA invariants" (Func.name fn) ()

    let check_dom ?(k = Fn.id) dom fn b b' =
      let l = Blk.label b in
      let l' = Blk.label b' in
      if Label.(l = l') then k ()
      else if not (Tree.is_descendant_of dom ~parent:l l')
      then fail fn

    (* The resolver should handle multiple definitions, as well as uses
       with no definitions. *)
    let go dom fn = match Resolver.create fn with
      | Error err -> failwith @@ Error.to_string_hum err
      | Ok r -> Func.blks fn |> Seq.iter ~f:(fun b ->
          (* Check that the use of each variable is dominated by
             its definition. We don't need to check the function
             arguments or slots because their scope is fixed. *)
          Blk.args b |> Seq.iter ~f:(fun x ->
              Resolver.uses r x |> List.iter ~f:(function
                  | `insn (_, b', _) | `blk b' ->
                    check_dom dom fn b b'));
          Blk.insns b |> Seq.iter ~f:(fun i ->
              Insn.lhs i |> List.iter ~f:(fun x ->
                  Resolver.uses r x |> List.iter ~f:(function
                      | `blk b' -> check_dom dom fn b b'
                      | `insn (i', b', _) ->
                        check_dom dom fn b b' ~k:(fun () ->
                            (* Check that `i` is defined before `i'`. *)
                            let l = Insn.label i in
                            let l' = Insn.label i' in
                            Blk.insns b' |> Seq.fold_until
                              ~init:() ~finish:Fn.id ~f:(fun () x ->
                                  if Insn.has_label x l then Stop ()
                                  else if Insn.has_label x l' then fail fn
                                  else Continue ()))))))
  end

  let try_ fn f = try Ok (f ()) with
    | Missing_blk l ->
      Or_error.errorf
        "SSA: missing block %a in function $%s"
        Label.pps l (Func.name fn)
    | Invalid_argument msg | Failure msg ->
      Or_error.errorf "SSA: %s" msg

  let run fn = try_ fn @@ fun () ->
    if Dict.mem (Func.dict fn) Tags.ssa
    then fn
    else
      let env = init fn in
      Phi.go env;
      Rename.go env;
      let fn =
        Hashtbl.data env.blks |>
        Func.update_blks_exn fn in
      Check.go env.dom fn;
      Func.with_tag fn Tags.ssa ()

  let check fn = try_ fn @@ fun () ->
    let cfg = Cfg.create fn in
    let dom = Graphlib.dominators (module Cfg) cfg Label.pseudoentry in
    Check.go dom fn
end
