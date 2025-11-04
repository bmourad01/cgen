open Core
open Regular.Std
open Graphlib.Std

module Scalar = struct
  module T = struct
    type t = Var.t * int64 [@@deriving equal, compare, sexp]
  end
  include T
  module Map = Map.Make(T)
end

type scalar = Scalar.t [@@deriving equal, sexp]

module Scalars = struct
  type t = Virtual.slot Scalar.Map.t
  let empty : t = Scalar.Map.empty
  let find (m : t) slot offset = Map.find m (slot, offset)
  let mem (m : t) slot offset = Map.mem m (slot, offset)
  let add (m : t) slot offset data = Map.set m ~key:(slot, offset) ~data
end

type scalars = Scalars.t

type value =
  | Top
  | Bottom
  | Offset of scalar
[@@deriving equal, sexp]

module Value = struct
  type t = value [@@deriving equal, sexp]

  let merge a b = match a, b with
    | Offset s1, Offset s2 when equal_scalar s1 s2 -> a
    | Offset _, Offset _ -> Top
    | Top, _  | _, Top -> Top
    | Bottom, _ -> b
    | _, Bottom -> a
end

module State = struct
  type t = value Var.Map.t [@@deriving equal, sexp]

  let merge (a : t) (b : t) =
    Map.merge_skewed a b ~combine:(fun ~key:_ a b -> Value.merge a b)

  let derive (s : t) ptr offset = match Map.find s ptr with
    | Some Offset (ptr', offset') -> Offset (ptr', Int64.(offset + offset'))
    | Some (Top | Bottom as v) -> v
    | None -> Bottom
end

type state = State.t [@@deriving equal, sexp]

(* XXX: do we need this? *)
(* let escaping fv x s = *)
(*   Set.fold (fv x) ~init:s ~f:(fun s v -> *)
(*       match Map.find s v with *)
(*       | Some Offset (ptr, _) -> Map.set s ~key:ptr ~data:Top *)
(*       | Some _ | None -> s) *)

module type L = sig
  module Insn : sig
    type t
    type op
    val op : t -> op
    val label : t -> Label.t
    val load_or_store_to : op -> (Var.t * Type.basic) option
    val subst_load_or_store : op -> f:(Var.t -> Var.t) -> op
    val offset : op -> scalar option
    val lhs : op -> Var.t option
    val free_vars : op -> Var.Set.t

    (* TODO: should we just do this? *)
    (* val transfer : state -> op -> state *)
  end

  module Ctrl : sig
    type t
    val free_vars : t -> Var.Set.t
  end

  module Blk : sig
    type t
    val label : t -> Label.t
    val insns : ?rev:bool -> t -> Insn.t seq
    val ctrl : t -> Ctrl.t
    val map_insns : t -> f:(Label.t -> Insn.op -> Insn.op) -> t
  end

  module Func : sig
    type t
    val slots : ?rev:bool -> t -> Virtual.slot seq
    val blks : ?rev:bool -> t -> Blk.t seq
    val map_of_blks : t -> Blk.t Label.Tree.t
    val map_blks : t -> f:(Blk.t -> Blk.t) -> t
    val insert_slot : t -> Virtual.slot -> t
  end

  module Cfg : sig
    include Label.Graph_s
    val create : Func.t -> t
  end
end

module Make(M : L) : sig
  val run : M.Func.t -> M.Func.t Context.t
end = struct
  open M

  let transfer_op s op =
    let value = match Insn.offset op with
      | Some (ptr, offset) -> State.derive s ptr offset
      | None -> Bottom in
    let s = match Insn.lhs op with
      | Some lhs -> Map.set s ~key:lhs ~data:value
      | None -> s in
    match value with
    | Bottom | Top ->
      (* escaping Insn.free_vars op s *)
      s
    | Offset _ -> s

  let transfer_insn s i = transfer_op s @@ Insn.op i

  let transfer blks l s =
    Label.Tree.find blks l |>
    Option.value_map ~default:s ~f:(fun b ->
        let s = Blk.insns b |> Seq.fold ~init:s ~f:transfer_insn in
        (* escaping Ctrl.free_vars (Blk.ctrl b) s *)
        s
      )

  let initialize fn =
    let slots =
      Func.slots fn |> Seq.fold ~init:Var.Map.empty ~f:(fun acc s ->
          let key = Virtual.Slot.var s in
          let data = Offset (key, 0L) in
          Map.set acc ~key ~data) in
    let nodes = Label.Map.singleton Label.pseudoentry slots in
    Solution.create nodes Var.Map.empty

  let analyze fn =
    let cfg = Cfg.create fn in
    let blks = Func.map_of_blks fn in
    Graphlib.fixpoint (module Cfg) cfg
      ~init:(initialize fn)
      ~start:Label.pseudoentry
      ~equal:State.equal
      ~merge:State.merge
      ~f:(transfer blks)

  let build_scalar_map fn s : scalars Context.t =
    let open Context.Syntax in
    Func.blks fn |> Context.Seq.fold ~init:Scalars.empty ~f:(fun acc b ->
        let s = Solution.get s @@ Blk.label b in
        Format.eprintf "%a: %a\n%!" Label.pp (Blk.label b) Sexp.pp_hum (sexp_of_state s);
        Blk.insns b |> Context.Seq.fold ~init:(acc, s) ~f:(fun (acc, s) i ->
            let op = Insn.op i in
            let s' = transfer_insn s i in
            let+ acc =
              match Insn.load_or_store_to op with
              | None -> !!acc
              | Some (ptr, ty) -> match Map.find s ptr with
                | Some Offset (slot, offset)
                  when Scalars.mem acc slot offset -> !!acc
                | Some Offset (slot, offset) ->
                  let* x = Context.Var.fresh in
                  let size = Type.sizeof_basic ty / 8 in
                  let*? slot' = Virtual.Slot.create x ~size ~align:size in
                  !!(Scalars.add acc slot offset slot')
                | _ -> !!acc in
            acc, s') >>| fst)

  let insert_new_slots fn (m : scalars) =
    Map.fold m ~init:fn ~f:(fun ~key:_ ~data:s fn ->
        Func.insert_slot fn s)

  let rewrite fn s m =
    Func.map_blks fn ~f:(fun b ->
        let s = ref @@ Solution.get s @@ Blk.label b in
        Blk.map_insns b ~f:(fun _ op ->
            let op' = match Insn.load_or_store_to op with
              | None -> op
              | Some (ptr, _) -> match Map.find !s ptr with
                | Some Offset (slot, offset) ->
                  Scalars.find m slot offset |>
                  Option.value_map ~default:op ~f:(fun s ->
                      Insn.subst_load_or_store op ~f:(fun x ->
                          if Var.(x <> ptr) then x
                          else Virtual.Slot.var s))
                | _ -> op in
            s := transfer_op !s op;
            op'))

  let run fn =
    let open Context.Syntax in
    let s = analyze fn in
    let+ m = build_scalar_map fn s in
    let fn = insert_new_slots fn m in
    rewrite fn s m
end
