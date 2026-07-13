open Core

module Slot = Virtual.Slot
module Vtree = Var.Tree
module VS = Var.Dense_set
module LS = Label.Dense_set
module LT = Label.Dense_table
module Solution = Fixpoint.Solution

type interval = {
  lo : int;
  hi : int;
} [@@deriving compare, sexp, equal]

module Interval = struct
  let pp ppf t = Format.fprintf ppf "[%d,%d]" t.lo t.hi

  let from_access off ty =
    let lo = Int64.to_int_exn off in
    let sz = Type.sizeof_basic ty / 8 in
    {lo; hi = lo + sz - 1}
end

module Runs = struct
  type t =
    | Nil
    | Run of {
        lo : int;
        hi : int;
        rest : t;
      }

  let rec equal a b = phys_equal a b || match a, b with
    | Nil, Nil -> assert false (* covered by `phys_equal` *)
    | Run x, Run y ->
      x.lo = y.lo && x.hi = y.hi && equal x.rest y.rest
    | _ -> false

  let empty = Nil
  let singleton lo hi = Run {lo; hi; rest = Nil} [@@inline]

  let[@tail_mod_cons] rec to_list = function
    | Run {lo; hi; rest} -> {lo; hi} :: to_list rest
    | Nil -> []

  let[@tail_mod_cons] rec add t lo hi = match t with
    | Nil -> Run {lo; hi; rest = Nil}
    | Run r ->
      if r.hi + 1 < lo then
        Run {r with rest = add r.rest lo hi}
      else if hi + 1 < r.lo then
        Run {lo; hi; rest = t}
      else add r.rest (min lo r.lo) (max hi r.hi)

  let[@tail_mod_cons] rec inter a b = match a, b with
    | Nil, _ | _, Nil -> Nil
    | Run x, Run y ->
      let lo = max x.lo y.lo and hi = min x.hi y.hi in
      let na, nb =
        if x.hi < y.hi then x.rest, b
        else if y.hi < x.hi then a, y.rest
        else x.rest, y.rest in
      if lo <= hi
      then Run {lo; hi; rest = inter na nb}
      else inter na nb

  let rec dominates t lo hi = match t with
    | Nil -> false
    | Run r when lo < r.lo -> false
    | Run r -> hi <= r.hi || dominates r.rest lo hi
end

(* For each slot, the set of relative byte offsets initialized by a store. *)
type state = Runs.t Vtree.t

let equal_state s1 s2 = Vtree.equal Runs.equal s1 s2

let empty_state : state = Vtree.empty

(* Starting constraint has the entry block with no incoming
   initializations. *)
let init_constraints : state Label.Tree.t =
  Label.Tree.singleton Label.pseudoentry empty_state

(* Our top element, which is every slot having been initialized. *)
let top_state slots : state =
  Vtree.mapi slots ~f:(fun ~key:_ ~data:s ->
      Runs.singleton 0 (Slot.size s - 1))

(* Since this is a "must" forward-flow analysis, incoming
   predecessor states must intersect. *)
let merge_state s1 s2 =
  Vtree.inter_with s1 s2 ~f:(fun ~key:_ t1 t2 ->
      if phys_equal t1 t2 then t1 else Runs.inter t1 t2)

type solution = state Solution.t

type t = {
  soln : solution;
  bad  : LS.t;
}

(* If the slot is not always initialized by the
   time we reach the load, then we have UB. *)
let is_uninitialized acc base off ty =
  match Vtree.find acc base with
  | None -> true
  | Some t ->
    let {lo; hi} = Interval.from_access off ty in
    not (Runs.dominates t lo hi)

type access =
  | Load_at  of Var.t * int64 * Type.basic
  | Store_at of Var.t * int64 * Type.basic

let apply_store acc base off ty =
  let {lo; hi} = Interval.from_access off ty in
  Vtree.update_with acc base
    ~nil:(fun () -> Runs.singleton lo hi)
    ~has:(fun t ->
        if Runs.dominates t lo hi then t
        else Runs.add t lo hi)

let apply_load bad acc l base off ty =
  if is_uninitialized acc base off ty then LS.add bad l;
  acc

let debug_dump blks bad s =
  Logs.debug (fun m ->
      Label.Tree.iter blks ~f:(fun ~key ~data:_ ->
          let s = Solution.get s key in
          let pp_tree ppf (x, t) =
            Format.fprintf ppf "%a:@[{%a}@]" Var.pp x
              (Format.pp_print_list
                 ~pp_sep:(fun ppf () -> Format.pp_print_string ppf ", ")
                 Interval.pp)
              (Runs.to_list t) in
          m "%s: %a: incoming must-initialize: %s%!"
            __FUNCTION__ Label.pp key
            (Vtree.to_list s |>
             List.to_string ~f:(Format.asprintf "%a" pp_tree))));
  Logs.debug (fun m ->
      LS.iter bad ~f:(fun l ->
          m "%s: load at %a is potentially uninitialized%!"
            __FUNCTION__ Label.pp l))

module Make(M : Scalars.L) = struct
  open M

  module S = Scalars.Make(M)

  let collect_accesses t blks slots =
    let ninsns =
      Label.Tree.fold blks ~init:0
        ~f:(fun ~key:_ ~data:b acc -> acc + Blk.num_insns b) in
    let accesses = LT.create ~capacity:ninsns () in
    Label.Tree.iter blks ~f:(fun ~key:l ~data:b ->
        let s = ref @@ Scalars.get t l in
        Blk.iter_insns b ~f:(fun i ->
            let op = Insn.op i in
            begin match Insn.load_or_store_to op with
              | Some (ptr, ty, kind) ->
                begin match Vtree.find !s ptr with
                  | Some Offset (base, off) ->
                    begin match kind with
                      | Load ->
                        LT.set accesses ~key:(Insn.label i)
                          ~data:(Load_at (base, off, ty))
                      | Store ->
                        (* An escaped slot is never considered initialized. *)
                        if VS.mem t.esc base then
                          Logs.debug (fun m ->
                              m "%s: ignoring escaped slot %a%!"
                                __FUNCTION__ Var.pp base)
                        else
                          LT.set accesses ~key:(Insn.label i)
                            ~data:(Store_at (base, off, ty))
                    end
                  | _ -> ()
                end
              | None -> ()
            end;
            s := S.transfer_op slots !s op));
    accesses

  let transfer bad accesses blks l st =
    match Label.Tree.find blks l with
    | None -> st
    | Some b ->
      Blk.fold_insns b ~init:st ~f:(fun acc i ->
          let l = Insn.label i in
          match LT.find accesses l with
          | Some (Store_at (base, off, ty)) ->
            apply_store acc base off ty
          | Some (Load_at (base, off, ty)) ->
            apply_load bad acc l base off ty
          | None -> acc)

  let analyze' t cfg blks slots =
    let bad = LS.create () in
    let accesses = collect_accesses t blks slots in
    let s = Fixpoint.run cfg
        ~init:(Solution.create init_constraints @@ top_state slots)
        ~start:Label.pseudoentry
        ~equal:equal_state
        ~merge:merge_state
        ~f:(transfer bad accesses blks) in
    debug_dump blks bad s;
    {soln = s; bad}

  let analyze cfg blks slots =
    let t = S.analyze cfg blks slots in
    analyze' t cfg blks slots
end
