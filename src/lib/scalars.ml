open Core
open Regular.Std
open Graphlib.Std

let (@.) = Fn.compose
let (@<) = Fn.flip

(* A scalar access. *)
module Scalar = struct
  module T = struct
    type t = Var.t * int64 [@@deriving compare, equal, hash, sexp]
  end
  include T
  module Map = Map.Make(T)
  module Table = Hashtbl.Make(T)
end

type scalar = Scalar.t [@@deriving compare, equal, hash, sexp]
type scalars = Virtual.slot Scalar.Map.t

(* Lattice of scalar accesses.

   [Top]: the access is inconsistent or escapes

   [Offset (s, o)]: access to slot [s] at offset [o]
*)
type value =
  | Top
  | Offset of scalar
[@@deriving equal, sexp]

let pp_value ppf = function
  | Top -> Format.fprintf ppf "\u{22a4}"
  | Offset (slot, offset) ->
    let neg = Int64.is_negative offset in
    let pre, off = if neg then '-', Int64.neg offset else '+', offset in
    Format.fprintf ppf "%a%c0x%Lx" Var.pp slot pre off

let pp_bot ppf () = Format.fprintf ppf "\u{22a5}" [@@ocaml.warning "-32"]

module Value = struct
  type t = value [@@deriving equal, sexp]
  let merge a b = match a, b with
    | Offset s1, Offset s2 when equal_scalar s1 s2 -> a
    | _ -> Top
end

type slots = Virtual.slot Var.Map.t

module State : sig
  type t = value Var.Map.t [@@deriving equal, sexp]
  val empty : t
  val merge : t -> t -> t
  val derive : slots -> t -> Var.t -> int64 -> value option
end = struct
  (* NB: the keys are the LHS of a given instruction *)
  type t = value Var.Map.t [@@deriving equal, sexp]

  let empty = Var.Map.empty

  let merge a b = Map.merge_skewed a b
      ~combine:(fun ~key:_ a b -> Value.merge a b)

  let is_bad slots ptr offset =
    Int64.(offset < 0L) || match Map.find slots ptr with
    | Some s ->
      let size = Int64.of_int @@ Virtual.Slot.size s in
      Int64.(offset >= size)
    | None -> false

  (* Normalize the scalar referred to by `ptr` and `offset`. *)
  let derive slots s ptr offset = match Map.find s ptr with
    | (Some Top | None) as v -> v
    | Some Offset (ptr', offset') ->
      let offset'' = Int64.(offset + offset') in
      (* Out of bounds offset to a slot should be undefined. *)
      let value =
        if is_bad slots ptr' offset'' then Top
        else Offset (ptr', offset'') in
      Some value
end

type state = State.t [@@deriving equal, sexp]

let pp_state ppf s =
  let pp_sep ppf () = Format.fprintf ppf "@ " in
  let pp_elt ppf (x, v) = Format.fprintf ppf "(%a@ %a)" Var.pp x pp_value v in
  let pp_elts = Format.pp_print_list ~pp_sep pp_elt in
  Format.fprintf ppf "@[<hov 0>%a@]" pp_elts @@ Map.to_alist s
[@@ocaml.warning "-32"]

type solution = (Label.t, state) Solution.t

let empty_solution = Solution.create Label.Map.empty State.empty

type load_or_store = Load | Store

let pp_load_or_store ppf = function
  | Load -> Format.fprintf ppf "load"
  | Store -> Format.fprintf ppf "store"

let is_store = function
  | Load -> false
  | Store -> true

module type L = sig
  module Insn : sig
    type t
    type op

    val create : label:Label.t -> op -> t

    (* General accessors. *)
    val op : t -> op
    val label : t -> Label.t

    (* Used during analysis. *)
    val lhs : op -> Var.Set.t
    val offset : op -> scalar option
    val copy_of : op -> Var.t option
    val free_vars : op -> Var.Set.t
    val escapes : op -> Var.Set.t
    val special : op -> bool

    (* Used during replacement. *)
    val load_or_store_to : op -> (Var.t * Type.basic * load_or_store) option
    val replace_load_or_store_addr : Var.t -> op -> op
    val with_op : t -> op -> t
    val add : Var.t -> Type.imm_base -> Var.t -> int64 -> op
  end

  module Ctrl : sig
    type t
    val free_vars : t -> Var.Set.t
    val escapes : t -> Var.Set.t
    val locals : t -> (Label.t * Var.t list) list
  end

  module Blk : sig
    type t
    val label : t -> Label.t
    val args : ?rev:bool -> t -> Var.t seq
    val insns : ?rev:bool -> t -> Insn.t seq
    val ctrl : t -> Ctrl.t
    val with_insns : t -> Insn.t list -> t
  end

  module Func : sig
    type t
    val slots : ?rev:bool -> t -> Virtual.slot seq
    val blks : ?rev:bool -> t -> Blk.t seq
    val map_of_blks : t -> Blk.t Label.Tree.t
    val with_blks : t -> Blk.t list -> t Or_error.t
    val insert_slot : t -> Virtual.slot -> t
  end

  module Cfg : sig
    include Label.Graph_s
    val create : Func.t -> t
  end
end

module Make(M : L) = struct
  open M

  (* Set all known scalars to `Top` according to `f`, which is the
     set of variables that escape. *)
  let escaping f x s =
    Set.fold (f x) ~init:s ~f:(fun s v ->
        match Map.find s v with
        | Some Offset (ptr, _) ->
          Map.set s ~key:ptr ~data:Top
        | Some _ | None -> s)

  (* Transfer function for a single instruction. *)
  let transfer_op slots s op =
    let value = match Insn.offset op with
      | Some (ptr, offset) -> State.derive slots s ptr offset
      | None -> Insn.copy_of op |> Option.bind ~f:(Map.find s) in
    let s = match value with
      | None -> s
      | Some v ->
        Insn.lhs op |> Set.fold ~init:s
          ~f:(fun s key -> Map.set s ~key ~data:v) in
    escaping Insn.escapes op s

  let blkargs blks (l, xs) =
    Label.Tree.find blks l |>
    Option.value_map ~default:[] ~f:(fun b ->
        let args = Seq.to_list @@ Blk.args b in
        match List.zip xs args with
        | Unequal_lengths -> []
        | Ok args' -> args')

  (* Transfer for control-flow instruction. *)
  let transfer_ctrl blks s c =
    let init = escaping Ctrl.escapes c s in
    (* Propagate the block parameters we are passing. *)
    Ctrl.locals c |> List.bind ~f:(blkargs blks) |>
    List.fold ~init ~f:(fun acc (src, dst) ->
        if Var.(src = dst) then acc
        else match Map.find acc src with
          | Some v -> Map.set acc ~key:dst ~data:v
          | None -> acc)

  (* Transfer function for a block. *)
  let transfer slots blks l s =
    Label.Tree.find blks l |>
    Option.value_map ~default:s ~f:(fun b ->
        Blk.insns b |> Seq.map ~f:Insn.op |>
        Seq.fold ~init:s ~f:(transfer_op slots) |>
        transfer_ctrl blks @< Blk.ctrl b)

  (* Initial constraints. *)
  let initialize slots blks =
    (* Set all slots to point to their own base address. *)
    let init = Map.mapi slots ~f:(fun ~key ~data:_ -> Offset (key, 0L)) in
    (* Any slot that directly escapes should immediately be set to `Top`. *)
    Label.Tree.fold blks ~init ~f:(fun ~key:_ ~data init ->
        Blk.insns data |> Seq.fold ~init ~f:(fun s i ->
            escaping Insn.escapes (Insn.op i) s) |>
        escaping Ctrl.escapes (Blk.ctrl data)) |>
    Label.Map.singleton Label.pseudoentry |>
    Solution.create @< State.empty

  (* All slots mapped to their names. *)
  let collect_slots fn =
    Func.slots fn |> Seq.fold ~init:Var.Map.empty ~f:(fun acc s ->
        Map.set acc ~key:(Virtual.Slot.var s) ~data:s)

  (* Run the dataflow analysis. *)
  let analyze ?cfg ?blks slots fn : solution =
    let cfg = match cfg with
      | None -> Cfg.create fn
      | Some cfg -> cfg in
    let blks = match blks with
      | None -> Func.map_of_blks fn
      | Some blks -> blks in
    Graphlib.fixpoint (module Cfg) cfg
      ~init:(initialize slots blks)
      ~start:Label.pseudoentry
      ~equal:State.equal
      ~merge:State.merge
      ~f:(transfer slots blks)
end
