open Core
open Regular.Std
open Graphlib.Std
open Virtual

open Context.Syntax

module type L = sig
  type lhs

  module Insn : sig
    type op
    type t
    val label : t -> Label.t
    val store : t -> (operand * Var.t * Type.basic) option
    val load : t -> (Var.t * Type.basic) option
    val fibits : Var.t -> Type.fp -> operand -> op
    val ifbits : Var.t -> Type.imm_base -> operand -> op
    val copy : Var.t -> Type.basic -> operand -> op
  end

  module Blk : sig
    type t
    val label : t -> Label.t
    val insns : ?rev:bool -> t -> Insn.t seq
    val map_insns : t -> f:(Label.t -> Insn.op -> Insn.op) -> t
  end

  module Func : sig
    type t
    val name : t -> string
    val slots : ?rev:bool -> t -> slot seq
    val remove_slot : t -> Var.t -> t
    val map_blks : t -> f:(Blk.t -> Blk.t) -> t
  end

  module Cfg : sig
    include Label.Graph
    val create : Func.t -> t
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
    cfg  : Cfg.t;
    dom  : Label.t tree;
    ops  : Insn.op Label.Table.t;
  }

  let init fn =
    let*? reso = Resolver.create fn in
    let use = Use.compute fn in
    let cfg = Cfg.create fn in
    let dom = Graphlib.dominators (module Cfg) cfg Label.pseudoentry in
    let ops = Label.Table.create () in
    !!{fn; use; reso; cfg; dom; ops}

  module Qualify = struct
    (* The qualification of the slot.

       `Bad`: the slot's usage is either unknown or is inconsistent with
       promotion.

       `Size n`: the slot is known to have been read at size `n`.

       `Tsize (n, t)`: the slot is known to have been read at size `n`,
       stored at size `n` and type `t`, or both.
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
      Seq.fold_until ~init:Bad ~finish:Fn.id ~f:(fun acc u ->
          match Resolver.resolve env.reso u with
          | Some `blk _ | None -> Stop Bad
          | Some `insn (i, _, _) -> match infer acc x i with
            | (Read _ | Write _) as acc -> Continue acc
            | Bad -> Stop Bad)
  end

  let collect env =
    Func.slots env.fn |>
    Context.Seq.fold ~init:Var.Map.empty ~f:(fun acc s ->
        match Qualify.go env s with
        | Bad -> !!acc
        | Write (_, t) -> !!(Var.Map.set acc ~key:(Slot.var s) ~data:t)
        | Read _ ->
          Context.failf
            "In Promote_slots: slot %a in function $%s is read but never stored to"
            Var.pp (Slot.var s) (Func.name env.fn) ())

  let remove fn =
    Var.Map.fold ~init:fn ~f:(fun ~key ~data:_ fn ->
        Func.remove_slot fn key)

  (* Replace a store with a copy to a fresh variable. *)
  let replace_store env subst x l v t =
    let+ y = Context.Var.fresh in
    let k = Insn.copy y t v in
    Hashtbl.set env.ops ~key:l ~data:k;
    Map.set subst ~key:x ~data:y

  (* Replace a load with a copy/cast. *)
  let replace_load env subst b x l y t t' = match Map.find subst x with
    | None ->
      (* This would be a violation the SSA property. *)
      Context.failf
        "In Promote_slots: slot %a in function $%s is read at \
         instruction %a in block %a before it is stored to"
        Var.pp x (Func.name env.fn) Label.pp l Label.pp (Blk.label b) ()
    | Some x ->
      let k = match t', t with
        | #Type.imm_base as imm, #Type.fp -> Insn.ifbits y imm (`var x)
        | #Type.fp as fp, #Type.imm_base -> Insn.fibits y fp (`var x)
        | _ -> Insn.copy y t' (`var x) in
      Hashtbl.set env.ops ~key:l ~data:k;
      !!subst

  let step env u x t subst l = match Resolver.resolve env.reso l with
    | None -> !!subst
    | Some `insn _ -> assert false
    | Some `blk b ->
      Blk.insns b |>
      Context.Seq.fold ~init:subst ~f:(fun subst i ->
          let l = Insn.label i in
          match Insn.store i with
          | Some (v, _, _) when Set.mem u l ->
            replace_store env subst x l v t
          | Some _ -> !!subst
          | None -> match Insn.load i with
            | Some (y, t') when Set.mem u l ->
              replace_load env subst b x l y t t'
            | Some _ | None -> !!subst)

  let replace env x t =
    let rec loop u q = match Stack.pop q with
      | None -> !!()
      | Some (l, subst) ->
        let* subst = step env u x t subst l in
        Tree.children env.dom l |>
        Seq.iter ~f:(fun l -> Stack.push q (l, subst));
        loop u q in
    let u = Use.find env.use x |> Label.Set.of_sequence in
    loop u @@ Stack.singleton (Label.pseudoentry, Var.Map.empty)

  let run fn =
    let* env = init fn in
    let* xs = collect env in
    let fn = remove fn xs in
    let+ () =
      Map.to_sequence xs |>
      Context.Seq.iter ~f:(fun (x, t) -> replace env x t) in
    Func.map_blks fn ~f:(fun b ->
        Blk.map_insns b ~f:(fun l default ->
            Hashtbl.find env.ops l |>
            Option.value ~default))
end
