(* A conservative implementation of SROA (Scalar Replacement of Aggregates).

   Most notably, we don't consider compound/aggregate types at all. Why?
   Because they are second-class citizens in our IR, and they are highly
   dependent on the implementation details of the target ABI.

   After ABI lowering, they are desugared, after which this pass becomes
   more useful.
*)

open Core
open Regular.Std
open Graphlib.Std

let debug = false

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
  | Offset (slot, offset) -> Format.fprintf ppf "%a+0x%Lx" Var.pp slot offset

let pp_bot ppf () = Format.fprintf ppf "\u{22a5}" [@@ocaml.warning "-32"]

module Value = struct
  type t = value [@@deriving equal, sexp]

  (* Join two abstract values. *)
  let merge a b = match a, b with
    | Offset s1, Offset s2 when equal_scalar s1 s2 -> a
    | Offset _, Offset _ -> Top
    | Top, _  | _, Top -> Top
end

type slots = Virtual.slot Var.Map.t

module State : sig
  type t = value Var.Map.t [@@deriving equal, sexp]
  val merge : t -> t -> t
  val derive : slots -> t -> Var.t -> int64 -> value option
end = struct
  (* NB: the keys are the LHS of a given instruction *)
  type t = value Var.Map.t [@@deriving equal, sexp]

  let merge a b = Map.merge_skewed a b
      ~combine:(fun ~key:_ a b -> Value.merge a b)

  let is_bad slots ptr offset =
    Int64.(offset < 0L) || match Map.find slots ptr with
    | Some s ->
      let size = Int64.of_int @@ Virtual.Slot.size s in
      Int64.(offset >= size)
    | None -> false

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
  let pp_elt ppf (x, v) = Format.fprintf ppf "%a[%a]" Var.pp x pp_value v in
  let pp_elts = Format.pp_print_list ~pp_sep pp_elt in
  Format.fprintf ppf "@[<hov 0>%a@]" pp_elts @@ Map.to_alist s
[@@ocaml.warning "-32"]

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
    val lhs : op -> Var.t option
    val offset : op -> scalar option
    val copy_of : op -> Var.t option
    val escapes : op -> Var.Set.t

    (* Used during replacement. *)
    val load_or_store_to : op -> (Var.t * Type.basic * load_or_store) option
    val subst_load_or_store : f:(Var.t -> Var.t) -> op -> op
    val with_op : t -> op -> t
    val add : Var.t -> Type.imm_base -> Var.t -> int64 -> op
  end

  module Ctrl : sig
    type t
    val escapes : t -> Var.Set.t
  end

  module Blk : sig
    type t
    val label : t -> Label.t
    val insns : ?rev:bool -> t -> Insn.t seq
    val ctrl : t -> Ctrl.t
    val map_insns : t -> f:(Label.t -> Insn.op -> Insn.op) -> t
    val with_insns : t -> Insn.t list -> t
  end

  module Func : sig
    type t
    val slots : ?rev:bool -> t -> Virtual.slot seq
    val blks : ?rev:bool -> t -> Blk.t seq
    val map_of_blks : t -> Blk.t Label.Tree.t
    val map_blks : t -> f:(Blk.t -> Blk.t) -> t
    val with_blks : t -> Blk.t list -> t Or_error.t
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

  let escaping f x s =
    Set.fold (f x) ~init:s ~f:(fun s v ->
        match Map.find s v with
        | Some Offset (ptr, _) ->
          Map.set s ~key:ptr ~data:Top
        | Some _ | None -> s)

  let transfer_op slots s op =
    let value = match Insn.offset op with
      | Some (ptr, offset) -> State.derive slots s ptr offset
      | None -> Insn.copy_of op |> Option.bind ~f:(Map.find s) in
    let s = match value, Insn.lhs op with
      | Some v, Some lhs -> Map.set s ~key:lhs ~data:v
      | None, _ | _, None -> s in
    escaping Insn.escapes op s

  let transfer slots blks l s =
    Label.Tree.find blks l |>
    Option.value_map ~default:s ~f:(fun b ->
        Blk.insns b |> Seq.map ~f:Insn.op |>
        Seq.fold ~init:s ~f:(transfer_op slots) |>
        escaping Ctrl.escapes (Blk.ctrl b))

  let initialize slots blks =
    (* Set all slots to point to their own base address. *)
    let slots = Map.mapi slots ~f:(fun ~key ~data:_ -> Offset (key, 0L)) in
    (* Any slot that escapes should immediately be set to `Top`. *)
    let slots =
      Label.Tree.fold blks ~init:slots ~f:(fun ~key:_ ~data init ->
          Blk.insns data |> Seq.fold ~init ~f:(fun s i ->
              escaping Insn.escapes (Insn.op i) s) |>
          escaping Ctrl.escapes (Blk.ctrl data)) in
    (* Start at pseudoentry. *)
    let nodes = Label.Map.singleton Label.pseudoentry slots in
    Solution.create nodes Var.Map.empty

  let analyze slots fn =
    let cfg = Cfg.create fn in
    let blks = Func.map_of_blks fn in
    Graphlib.fixpoint (module Cfg) cfg
      ~init:(initialize slots blks)
      ~start:Label.pseudoentry
      ~equal:State.equal
      ~merge:State.merge
      ~f:(transfer slots blks)

  let collect_slots fn =
    Func.slots fn |> Seq.fold ~init:Var.Map.empty ~f:(fun acc s ->
        Map.set acc ~key:(Virtual.Slot.var s) ~data:s)

  let is_base s offset size = match offset with
    | 0L -> Virtual.Slot.size s = size
    | _ -> false

  (* A memory access for a slot. *)
  type access = {
    insn : Insn.t;
    off  : int64;
    ty   : Type.basic;
    ldst : load_or_store;
  }

  let cmp_access a b = Int64.compare a.off b.off

  let pp_access ppf a =
    Format.fprintf ppf "%a[%a.%a +0x%Lx]"
      Label.pp (Insn.label a.insn)
      pp_load_or_store a.ldst
      Type.pp_basic a.ty
      a.off

  let collect_accesses slots fn s : access list Var.Map.t =
    (* Group all memory accesses by their corresponding slot. *)
    Func.blks fn |> Seq.fold ~init:Var.Map.empty ~f:(fun init b ->
        let s = ref @@ Solution.get s @@ Blk.label b in
        Blk.insns b |> Seq.fold ~init ~f:(fun acc i ->
            let op = Insn.op i in
            let acc = match Insn.load_or_store_to op with
              | None -> acc
              | Some (ptr, ty, ldst) -> match Map.find !s ptr with
                | Some Offset (base, off) ->
                  Map.add_multi acc ~key:base ~data:{insn = i; off; ty; ldst}
                | _ -> acc in
            s := transfer_op slots !s op;
            acc)) |>
    (* Filter out slots that are not splittable. *)
    Map.map ~f:(List.sort ~compare:cmp_access) |>
    Map.filteri ~f:(fun ~key ~data ->
        let rec ok = function
          | [] | [_] -> true
          | x :: y :: rest ->
            let sz = Type.sizeof_basic x.ty / 8 in
            ((* No partial overlaps. *)
              Int64.(x.off + of_int sz <= y.off) ||
              (* Allow exact re-use of the same region. *)
              Int64.(x.off = y.off) && Type.equal_basic x.ty y.ty
            ) && ok (y :: rest) in
        let res = ok data in
        if debug && not res then
          Format.eprintf "filtering out accesses for %a\n%!" Var.pp key;
        res)

  let overlaps oa sa ob sb =
    Int64.(oa < ob + of_int sb && ob < oa + of_int sa)

  type partition = {
    off  : int64;
    size : int;
    mems : access list;
  }

  let cmp_partition a b = Int64.compare a.off b.off

  let pp_partition ppf p =
    Format.fprintf ppf "0x%Lx:%d: (%a)"
      p.off p.size
      (Format.pp_print_list
         ~pp_sep:(fun ppf () -> Format.fprintf ppf ", ")
         pp_access) p.mems

  let partition_acesses m : partition list Var.Map.t =
    let rec merge acc c = function
      | [] -> List.sort (c :: acc) ~compare:cmp_partition
      | x :: xs ->
        let sx = Type.sizeof_basic x.ty / 8 in
        if overlaps c.off c.size x.off sx then
          let o' = Int64.min c.off x.off in
          let ec = Int64.(c.off + of_int c.size) in
          let ex = Int64.(x.off + of_int sx) in
          let e' = Int64.max ec ex in
          let s' = Int64.(to_int_exn (e' - o')) in
          merge acc {
            off = o';
            size = s';
            mems = x :: c.mems;
          } xs
        else
          merge (c :: acc) {
            off = x.off;
            size = sx;
            mems = [x];
          } xs in
    Map.map m ~f:(fun (accesses : access list) ->
        List.sort accesses ~compare:(fun a b ->
            Int64.compare a.off b.off) |> function
        | [] -> []
        | (x : access) :: xs ->
          merge [] {
            off = x.off;
            size = Type.sizeof_basic x.ty / 8;
            mems = [x];
          } xs)

  (* Turn each partition into a concrete slot. *)
  let materialize_partitions slots m =
    let open Context.Syntax in
    Map.to_sequence m |> Context.Seq.fold
      ~init:Scalar.Map.empty ~f:(fun init (base, ps) ->
          let s = Map.find_exn slots base in
          List.filter ps ~f:(fun p ->
              not @@ is_base s p.off p.size) |>
          Context.List.fold ~init ~f:(fun acc p ->
              let* x = Context.Var.fresh in
              let*? s = Virtual.Slot.create x ~size:p.size ~align:p.size in
              if debug then
                Format.eprintf "new slot %a, base=%a, off=0x%Lx, size=%d\n%!"
                  Var.pp x Var.pp base p.off p.size;
              !!(Map.set acc ~key:(base, p.off) ~data:s)))

  let cover_exact m base off size =
    Map.find m base |> Option.bind ~f:(fun ps ->
        let rec go o r acc = function
          | _ when r <= 0 -> Some (List.rev acc)
          | [] -> None
          | p :: ps ->
            let pe = Int64.(p.off + of_int p.size) in
            let re = Int64.(o + of_int r) in
            if Int64.(p.off <= o && re <= pe) then
              (* Request satisfies entire partition. *)
              Some (List.rev (p.off :: acc))
            else if Int64.(p.off = o) && p.size <= r then
              (* Request is partly covered by the partition. *)
              let o' = Int64.(o + of_int p.size) in
              go o' (r - p.size) (p.off :: acc) ps
            else if Int64.(p.off < o) then
              (* Partition starts before this request. *)
              go o r acc ps
            else None in
        go off size [] ps)

  (* pre: op is a store *)
  let split_into_parts op ptr base covers m =
    List.filter_map covers ~f:(fun o ->
        Map.find m (base, o) |> Option.map ~f:(fun s ->
            Insn.subst_load_or_store op
              ~f:(const @@ Virtual.Slot.var s)))

  let insert_new_slots fn m = Map.fold m ~init:fn
      ~f:(fun ~key:_ ~data fn -> Func.insert_slot fn data)

  let rewrite_one parts m s i =
    let open Context.Syntax in
    let op = Insn.op i in
    let* word = Context.target >>| Target.word in
    match Insn.load_or_store_to op with
    | None -> !![i]
    | Some (ptr, ty, load_or_store) ->
      if debug then
        Format.eprintf "%a: looking at %a.%a to %a\n%!"
          Label.pp (Insn.label i)
          pp_load_or_store load_or_store
          Type.pp_basic ty
          Var.pp ptr;
      let sz = Type.sizeof_basic ty / 8 in
      match Map.find !s ptr with
      | Some Top | None -> !![i]
      | Some Offset (base, off) ->
        match cover_exact parts base off sz with
        | Some [o] ->
          if debug then
            Format.eprintf "exact=0x%Lx, off=0x%Lx, base=%a\n%!" o off Var.pp base;
          let o' = Int64.(off - o) in
          begin match Map.find m (base, o) with
            | None -> !![i]
            | Some s when Int64.(o' = 0L) ->
              if debug then
                Format.eprintf "found slot %a\n%!" Var.pp (Virtual.Slot.var s);
              let op' = Insn.subst_load_or_store op ~f:(const @@ Virtual.Slot.var s) in
              !![Insn.with_op i op']
            | Some s ->
              if debug then
                Format.eprintf "found slot %a\n%!" Var.pp (Virtual.Slot.var s);
              let* l = Context.Label.fresh in
              let* y = Context.Var.fresh in
              let a = Insn.add y word (Virtual.Slot.var s) o' in
              let op' = Insn.subst_load_or_store op ~f:(const y) in !![
                Insn.create ~label:l a;
                Insn.with_op i op';
              ]
          end
        | Some covers when is_store load_or_store ->
          if debug then
            Format.eprintf "%a: splitting\n%!" Label.pp @@ Insn.label i;
          split_into_parts op ptr base covers m |>
          Context.List.map ~f:(fun op ->
              let+ l = Context.Label.fresh in
              Insn.create ~label:l op)
        | Some covers ->
          if debug then
            Format.eprintf "multi or no-part load: %d\n%!" (List.length covers);
          !![i]
        | None ->
          if debug then
            Format.eprintf "no parts found\n%!";
          !![i]

  let rewrite_with_partitions slots fn s parts m =
    let open Context.Syntax in
    let* blks =
      Func.blks fn |> Context.Seq.map ~f:(fun b ->
          let s = ref @@ Solution.get s @@ Blk.label b in
          let+ insns =
            Blk.insns b |> Context.Seq.map ~f:(fun i ->
                let+ is = rewrite_one parts m s i in
                s := transfer_op slots !s @@ Insn.op i;
                is)
            >>| Fn.compose List.concat Seq.to_list in
          Blk.with_insns b insns) >>| Seq.to_list in
    Context.lift_err @@ Func.with_blks fn blks

  let run fn =
    let open Context.Syntax in
    let slots = collect_slots fn in
    let s = analyze slots fn in
    let accs = collect_accesses slots fn s in
    let parts = partition_acesses accs in
    if debug then
      Map.iteri parts ~f:(fun ~key ~data ->
          Format.eprintf "partitions for %a:\n%!" Var.pp key;
          List.iter data ~f:(fun p ->
              Format.eprintf "  %a\n%!" pp_partition p));
    let* m = materialize_partitions slots parts in
    let fn = insert_new_slots fn m in
    rewrite_with_partitions slots fn s parts m
end
