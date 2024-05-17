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
  Hashtbl.set t.idest ~key:id ~data:l;
  Hashtbl.update t.lmoved l ~f:(function
      | None -> Iset.singleton id
      | Some s -> Iset.add s id)

(* Update when we union two nodes together. Should not be
   called if both IDs are the same. *)
let merge t a b u =
  assert (a <> b);
  (* Link the ID to the label, along with the union ID. *)
  let link id l =
    Hashtbl.set t.isrc ~key:id ~data:l;
    Hashtbl.set t.isrc ~key:u ~data:l in
  match Hashtbl.(find t.isrc a, find t.isrc b) with
  | None, None -> ()
  | None, Some pb -> link a pb
  | Some pa, None -> link b pa
  | Some pa, Some pb when Label.(pa = pb) -> ()
  | Some pa, Some pb when dominates t ~parent:pb pa -> link a pb
  | Some pa, Some pb when dominates t ~parent:pa pb -> link b pa
  | Some pa, Some pb ->
    let pc = lca t pa pb in
    let c = find t a in
    assert (c = find t b);
    assert (c = find t u);
    Hashtbl.remove t.isrc a;
    Hashtbl.remove t.isrc b;
    move t [pa; pb] pc c

(* We've matched on a value that we already hash-consed, so
   figure out which label it should correspond to. *)
let duplicate t id a = match Hashtbl.find t.isrc id with
  | Some b when Label.(b = a) -> ()
  | Some b when dominates t ~parent:b a -> ()
  | Some b when dominates t ~parent:a b ->
    Hashtbl.set t.isrc ~key:id ~data:a
  | Some b ->
    let c = lca t a b in
    Hashtbl.remove t.isrc id;
    move t [a; b] c @@ find t id
  | None ->
    (* Check if `id ` was moved up the tree. *)
    let cid = find t id in
    match Hashtbl.find t.idest cid with
    | None ->
      (* This e-class wasn't moved, though it wasn't registered
         to begin with (even though it was hash-consed). *)
      Hashtbl.set t.isrc ~key:id ~data:a
    | Some b when dominates t ~parent:b a ->
      (* Mark this e-class as being used at `a`. *)
      Hashtbl.update t.imoved cid ~f:(function
          | None -> Lset.singleton a
          | Some s -> Lset.add s a)
    | Some b when dominates t ~parent:a b -> move t [b] a cid
    | Some b -> move t [a; b] (lca t a b) cid

module Licm = struct
  let find_blk_loop t l = Loops.blk t.input.loop l

  let find_loop t l = match Resolver.resolve t.input.reso l with
    | Some (`blk b | `insn (_, b, _, _)) ->
      find_blk_loop t @@ Blk.label b
    | None -> assert false

  let is_child_loop t a b =
    not (Loops.equal_loop a b) &&
    Loops.is_child_of t.input.loop a b

  let id2label t id = match Hashtbl.find t.isrc id with
    | None -> Hashtbl.find t.idest id
    | Some _ as l -> l

  module Variance = struct
    (* Almost the same as `child`, but ignores the special cases
       thereof. *)
    let rec is_variant ~lp t l n = match find_loop t l with
      | Some lp' when is_child_loop t lp lp' -> false
      | Some _ -> children ~lp t n
      | None -> false

    (* Same as below, but we examine just the children of `n`. *)
    and children ~lp t n = match (n : enode) with
      | N (_, cs) -> List.exists cs ~f:(child ~lp t)
      | U {pre; post} ->
        (* XXX: do we want to default to the canonical ID here?
           We have to answer the question of whether the term
           could have been (soundly) rewritten such that it
           becomes invariant with respect to `lp`.

           Note that we ignore the case of rewriting to a constant,
           as they are marked as "subsuming" the previous term
           instead of being part of a tree of union nodes.
        *)
        let id = find t pre in
        assert (id = find t post);
        children ~lp t @@ node t id

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
              | Some lp' when is_child_loop t lp lp' ->
                (* The loop it belongs to is nested inside of the
                   current one. *)
                false
              | Some lp' when Loops.equal_loop lp lp' ->
                (* It's defined by a block within the current loop. *)
                true
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
      | n -> match id2label t id with
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

  let licm_move t l l' id =
    Hash_set.add t.licm id;
    move t [l] l' id

  (* We've determined that `n` is invariant with respect to `lp`, but
     if `lp` is nested in a parent loop `lp'`, then we should find out if
     `n` is also invariant with respect to `lp'`, and so on. *)
  let rec licm' t l n lp id =
    match Tree.parent t.input.dom @@ header t lp with
    | None -> assert false
    | Some l' -> match find_blk_loop t l' with
      | None -> licm_move t l l' id
      | Some lp' ->
        if Variance.children ~lp:lp' t n
        then licm_move t l l' id
        else licm' t l n lp' id

  let licm t l n lp id =
    if Variance.children ~lp t n
    then Hashtbl.set t.isrc ~key:id ~data:l
    else licm' t l n lp id
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
  | Some `blk _ -> Hashtbl.set t.isrc ~key:id ~data:l
  | Some `insn (i, _, _, _) when is_effectful t n i ->
    Hashtbl.set t.isrc ~key:id ~data:l
  | Some `insn _ -> match Licm.find_loop t l with
    | None -> Hashtbl.set t.isrc ~key:id ~data:l
    | Some lp -> Licm.licm t l n lp id
