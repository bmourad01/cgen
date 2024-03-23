open Core
open Monads.Std
open Regular.Std
open Virtual

module E = Monad.Result.Error

open E.Let

module type L = sig
  type lhs

  module Insn : sig
    type op
    type t
    val store : t -> (operand * Var.t * Type.basic) option
    val load : t -> (Var.t * Type.basic) option
    val fibits : Var.t -> Type.fp -> operand -> op
    val ifbits : Var.t -> Type.imm_base -> operand -> op
    val copy : Var.t -> Type.basic -> operand -> op
  end

  module Blk : sig
    type t
    val map_insns : t -> f:(Label.t -> Insn.op -> Insn.op) -> t
  end

  module Func : sig
    type t
    val name : t -> string
    val dict : t -> Dict.t
    val with_dict : t -> Dict.t -> t
    val slots : ?rev:bool -> t -> slot seq
    val remove_slot : t -> Var.t -> t
    val map_blks : t -> f:(Blk.t -> Blk.t) -> t
  end

  module Use : Use_intf.S with type func := Func.t

  module Resolver : Resolver_intf.S
    with type lhs := lhs
     and type insn := Insn.t
     and type blk := Blk.t
     and type func := Func.t
end

module Make(M : L) = struct
  open M

  type env = {
    fn   : Func.t;
    use  : Use.t;
    reso : Resolver.t;
    ops  : Insn.op Label.Table.t;
  }

  let init fn =
    let+ reso = Resolver.create fn in
    let use = Use.compute fn in
    let ops = Label.Table.create () in
    {fn; use; reso; ops}

  module Qualify = struct
    (* The qualification of the slot.

       `Bad`: the slot's usage is either unknown or is inconsistent with
       promotion.

       `Read n`: the slot is known to have been read at size `n`.

       `Write (n, t)`: the slot is known to have been written with size
       `n` and type `t`, and possibly read at size `n`.
    *)
    type t =
      | Bad
      | Read of int
      | Write of int * Type.basic

    (* Ensure that a slot is qualified for promotion, according to the
       following criteria:

       1. The slot is only used in load/store instructions.
       2. Each load/store size is the same.
       3. Each store type is the same.
       4. The slot itself is not the value being stored.
    *)
    let infer acc x i = match Insn.load i with
      | Some (_, t) ->
        let s = Type.sizeof_basic t in
        begin match acc with
          | Bad -> Read s
          | (Read s' | Write (s', _)) when s <> s' -> Bad
          | Read _ | Write _ -> acc
        end
      | None -> match Insn.store i with
        | None -> Bad
        | Some (`var v, _, _) when Var.(v = x) -> Bad
        | Some (_, a, _) when Var.(a <> x) -> Bad
        | Some (_, _, t) ->
          let s = Type.sizeof_basic t in
          match acc with
          | Bad -> Write (s, t)
          | (Read s' | Write (s', _)) when s <> s' -> Bad
          | Write (_, t') when not @@ Type.equal_basic t t' -> Bad
          | Read _ | Write _ -> Write (s, t)

    let go env s =
      let x = Slot.var s in
      Use.find env.use x |>
      Set.fold_until ~init:Bad ~finish:Fn.id ~f:(fun acc u ->
          match Resolver.resolve env.reso u with
          | Some `blk _ | None -> Stop Bad
          | Some `insn (i, _, _) -> match infer acc x i with
            | (Read _ | Write _) as acc -> Continue acc
            | Bad -> Stop Bad)
  end

  let collect env =
    Func.slots env.fn |>
    Seq.fold ~init:Var.Map.empty ~f:(fun acc s ->
        match Qualify.go env s with
        | Bad -> acc
        | Write (_, t) ->
          Var.Map.set acc ~key:(Slot.var s) ~data:t
        | Read _ ->
          (* In this case, we read from the slot but never stored anything
             to it. It's undefined behavior, but it's also what the programmer
             intended, so we should cancel this promotion. *)
          acc)

  let remove fn =
    Var.Map.fold ~init:fn ~f:(fun ~key ~data:_ fn ->
        Func.remove_slot fn key)

  (* Replace a store with a copy to a fresh variable. *)
  let replace_store env x l v t =
    Hashtbl.set env.ops ~key:l ~data:(Insn.copy x t v)

  (* Replace a load with a copy/cast. *)
  let replace_load env x l y t t' =
    let k = match t', t with
      | #Type.imm_base as imm, #Type.fp -> Insn.ifbits y imm (`var x)
      | #Type.fp as fp, #Type.imm_base -> Insn.fibits y fp (`var x)
      | _ -> Insn.copy y t' (`var x) in
    Hashtbl.set env.ops ~key:l ~data:k

  let replace env = Map.iteri ~f:(fun ~key:x ~data:t ->
      Use.find env.use x |> Set.iter ~f:(fun l ->
          match Resolver.resolve env.reso l with
          | None | Some `blk _ -> assert false
          | Some `insn (i, _, _) -> match Insn.store i with
            | Some (v, _, _) -> replace_store env x l v t
            | None -> match Insn.load i with
              | Some (y, t') -> replace_load env x l y t t'
              | None -> assert false))

  let run fn =
    let+ env = init fn in
    let xs = collect env in
    if not @@ Map.is_empty xs then
      let fn = remove fn xs in
      replace env xs;
      (* SSA form needs to be recomputed. *)
      let dict = Dict.remove (Func.dict fn) Tags.ssa in
      Func.with_dict fn dict |> Func.map_blks ~f:(fun b ->
          Blk.map_insns b ~f:(fun l default ->
              Hashtbl.find env.ops l |>
              Option.value ~default))
    else fn
end
