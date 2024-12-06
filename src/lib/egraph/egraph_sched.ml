(* Track the provenance between e-class IDs and labels in the CFG
   representation. This gets mainly used for the purpose of code
   motion when we extract back to the CFG form. *)

open Core
open Graphlib.Std
open Egraph_common
open Virtual

(* Immediate dominator. *)
let idom t l = match Tree.parent t.input.dom l with
  | Some l' -> l'
  | None ->
    (* The root is pseudoentry, which we should never reach. *)
    assert false

(* Lowest common ancestor in the dominator tree. Note that this
   should always be a block label. *)
let lca' t a b =
  let ra = ref a
  and rb = ref b
  and da = ref (Hashtbl.find_exn t.input.domd a)
  and db = ref (Hashtbl.find_exn t.input.domd b) in
  (* While `a` is deeper than `b`, go up the tree. *)
  while !da > !db do
    ra := idom t !ra;
    decr da;
  done;
  (* While `b` is deeper than `a`, go up the tree. *)
  while !db > !da do
    rb := idom t !rb;
    decr db;
  done;
  (* Find the common ancestor. *)
  while Label.(!ra <> !rb) do
    ra := idom t !ra;
    rb := idom t !rb;
  done;
  !ra

(* Resolve both labels to their corresponding blocks before we
   walk up the tree. *)
let lca t a b =
  let reso = Resolver.resolve t.input.reso in
  match reso a, reso b with
  | None, _ | _, None -> assert false
  | Some (`insn (_, ba, _, _) | `blk ba),
    Some (`insn (_, bb, _, _) | `blk bb) ->
    lca' t (Blk.label ba) (Blk.label bb)

(* Note that `id` must be the canonical e-class. *)
let move t old l id =
  Hashtbl.update t.imoved id ~f:(function
      | Some s -> List.fold old ~init:s ~f:Lset.add
      | None -> Lset.of_list old);
  Hashtbl.set t.ilbl ~key:id ~data:l;
  Hashtbl.update t.lmoved l ~f:(function
      | None -> Iset.singleton id
      | Some s -> Iset.add s id)

let mark_use t id a = Hashtbl.update t.imoved id ~f:(function
    | None -> Lset.singleton a
    | Some s -> Lset.add s a)

(* Update when we union two nodes together. Should not be
   called if both IDs are the same. *)
let merge t a b u =
  assert (a <> b);
  let cid = find t a in
  (* Link the ID to the label, along with the union ID. *)
  let link ?p l =
    Option.iter p ~f:(mark_use t cid);
    Hashtbl.set t.ilbl ~key:cid ~data:l;
    Hashtbl.set t.ilbl ~key:u ~data:l in
  match Hashtbl.(find t.ilbl a, find t.ilbl b) with
  | None, None -> ()
  | None, Some pb -> link pb
  | Some pa, None -> link pa
  | Some pa, Some pb when Label.(pa = pb) -> ()
  | Some pa, Some pb when dominates t ~parent:pb pa -> link pb ~p:pa
  | Some pa, Some pb when dominates t ~parent:pa pb -> link pa ~p:pb
  | Some pa, Some pb ->
    let pc = lca t pa pb in
    assert (cid = find t b);
    assert (cid = find t u);
    Hashtbl.remove t.ilbl a;
    Hashtbl.remove t.ilbl b;
    move t [pa; pb] pc cid

(* We've matched on a value that we already hash-consed, so
   figure out which label it should correspond to. *)
let duplicate t id a =
  let cid = find t id in
  match Hashtbl.find t.ilbl cid with
  | Some b when Label.(b = a) -> ()
  | Some b when dominates t ~parent:b a -> mark_use t cid a
  | Some b when dominates t ~parent:a b ->
    mark_use t cid b;
    Hashtbl.set t.ilbl ~key:id ~data:a
  | Some b ->
    let c = lca t a b in
    Hashtbl.remove t.ilbl cid;
    move t [a; b] c cid;
  | None ->
    (* This e-class wasn't moved, though it wasn't registered
       to begin with (even though it was hash-consed). *)
    Hashtbl.set t.ilbl ~key:cid ~data:a

module Licm = struct
  let is_child_loop ~parent t a = Loops.is_child_of ~parent t.input.loop a
  let find_blk_loop t l = Loops.blk t.input.loop l

  let find_loop t l = match Resolver.resolve t.input.reso l with
    | Some (`blk b | `insn (_, b, _, _)) ->
      find_blk_loop t @@ Blk.label b
    | None -> assert false

  module Variance = struct
    (* Almost the same as `child`, but ignores the special cases
       thereof. *)
    let rec is_variant ~lp t l n = match find_loop t l with
      | Some lp' when Loops.equal_loop lp lp' -> true
      | Some lp' when is_child_loop ~parent:lp' t lp -> false
      | Some _ -> children ~lp t n
      | None -> false

    (* Same as below, but we examine just the children of `n`. *)
    and children ~lp t n = match (n : enode) with
      | N (_, cs) -> List.exists cs ~f:(child ~lp t)
      | U {pre; post} ->
        (* We will take a conservative approach here. Since we can't
           predict whether the rewritten term is the one that will
           be extracted, we have to consider whether either terms are
           loop-variant. *)
        let go = Fn.compose (children ~lp t) (node t) in
        go pre || go post

    (* Generic entry point for determining of a node ID is variant
       w.r.t the loop `lp`.

       This has a lot of comments in an effort to convince myself
       that this is correct.
    *)
    and child ~lp t id = match node t id with
      | N (Ovar x, []) ->
        (* The node is a "free" variable, so it's restricted to a
           few scenarios, mainly related to whether it's an induction
           variable of the current loop or not. *)
        begin match Resolver.def t.input.reso x with
          | Some (`slot | `arg) ->
            (* Arguments and stack slots have scope for the entire
               function. *)
            false
          | Some `blkarg b ->
            (* It's block argument, so find out if it belongs to a
               loop. *)
            begin match find_blk_loop t @@ Blk.label b with
              | Some lp' when Loops.equal_loop lp lp' ->
                (* It's defined by a block within the current loop. *)
                true
              | Some lp' when is_child_loop ~parent:lp' t lp ->
                (* The loop it belongs to is nested inside of the
                   current one. *)
                false
              | Some _ ->
                (* It's defined in a loop, but not a child of the
                   current one. *)
                false
              | None ->
                (* It's not defined inside of any loop, so it's
                   invariant. *)
                false
            end
          | Some _ ->
            (* It's defined by some instruction that we can't move. *)
            true
          | None -> assert false
        end
      | n when Enode.is_const n ->
        (* If it's a constant then it is definitely invariant. *)
        false
      | n -> match Hashtbl.find t.ilbl id with
        | Some l ->
          (* Ask if where the node lives is variant with respect to
             the current loop. *)
          is_variant ~lp t l n
        | None ->
          (* We don't know where this node was defined or moved to,
             so we will play it safe and consider it variant. *)
          true
  end

  let header t lp = Loops.(header @@ get t.input.loop lp)

  let header_parent t lp =
    header t lp |> Tree.parent t.input.dom |> Option.value_exn

  let partition_uses t x =
    Resolver.uses t.input.reso x |>
    List.partition_map ~f:(function
        | `blk b | `insn (_, b, _, _) ->
          let l = Blk.label b in
          match find_blk_loop t l with
          | None -> First l
          | Some lp -> Second lp)

  let exists_in_loop t parent = List.exists ~f:(is_child_loop ~parent t)

  let licm_move t l l' lp id lhs =
    let l' = match lhs with
      | None -> l'
      | Some x -> match partition_uses t x with
        | [], [] -> l'
        | init :: xs, [] ->
          (* Never used inside of a loop. *)
          List.fold xs ~init ~f:(lca t)
        | _, ys when exists_in_loop t lp ys ->
          (* Pin at the current label if it's used in one of the
             loops we just hoisted out of. *)
          Hash_set.add t.pinned id;
          l'
        | xs, init :: ys ->
          (* Otherwise, find the common ancestor. *)
          Hash_set.add t.pinned id;
          let init = header_parent t init in
          List.fold ys ~init ~f:(fun acc lp ->
              lca t acc @@ header_parent t lp) |> fun init ->
          List.fold xs ~init ~f:(lca t) in
    move t [l] l' id

  (* We've determined that `n` is invariant with respect to `lp`, but
     if `lp` is nested in a parent loop `lp'`, then we should find out if
     `n` is also invariant with respect to `lp'`, and so on. *)
  let rec licm' t l n lp id lhs =
    let l' = header_parent t lp in
    match find_blk_loop t l' with
    | None -> licm_move t l l' lp id lhs
    | Some lp' ->
      if Variance.children ~lp:lp' t n
      then licm_move t l l' lp id lhs
      else licm' t l n lp' id lhs

  let licm t l n lp id lhs =
    if Variance.children ~lp t n
    then Hashtbl.set t.ilbl ~key:id ~data:l
    else licm' t l n lp id lhs
end

(* Verify that a div/rem instruction may trap. *)
let check_div_rem t : enode -> bool = function
  | N (Obinop (`div #Type.imm | `udiv _ | `rem #Type.imm | `urem _), [_; r]) ->
    begin match node t r with
      | N (Oint (i, _), []) -> Bv.(i = zero)
      | _ -> true
    end
  | _ -> false

let is_effectful t n i =
  Insn.can_load i ||
  Insn.is_effectful i ||
  check_div_rem t n

(* Track the provenance between the node and the label, but first see
   if we can do LICM (loop-invariant code motion). *)
let add t l id n = match Resolver.resolve t.input.reso l with
  | None -> assert false
  | Some `blk _ -> Hashtbl.set t.ilbl ~key:id ~data:l
  | Some `insn (i, _, _, _) when is_effectful t n i ->
    Hashtbl.set t.ilbl ~key:id ~data:l
  | Some `insn (_, b, lhs, _) ->
    match Licm.find_blk_loop t @@ Blk.label b with
    | None -> Hashtbl.set t.ilbl ~key:id ~data:l
    | Some lp -> Licm.licm t l n lp id lhs
