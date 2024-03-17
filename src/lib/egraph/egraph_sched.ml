(* Track the provenance between e-class IDs and labels in the CFG
   representation. *)

open Core
open Regular.Std
open Graphlib.Std
open Egraph_common
open Virtual

(* Lowest common ancestor in the dominator tree. Note that this
   should always be a block label. *)
let rec lca t a b =
  let p = Tree.parent t.input.cdom in
  match p a, p b with
  | Some a', Some b' when Label.(a' = b') -> a'
  | Some a', Some _  when dominates t ~parent:a' b -> a'
  | Some _,  Some b' when dominates t ~parent:b' a -> b'
  | Some a', Some b' when dominates t ~parent:a' b' -> a'
  | Some a', Some b' when dominates t ~parent:b' a' -> b'
  | Some a', Some b' -> lca t a' b'
  | None, _ | _, None ->
    (* The root is pseudoentry, which we should never reach. *)
    assert false

let move t old l id =
  let s = Label.Set.of_list old in
  Hashtbl.remove t.isrc id;
  Hashtbl.update t.imoved id ~f:(function
      | Some s' -> Set.union s s'
      | None -> s);
  Hashtbl.set t.idest ~key:id ~data:l;
  Hashtbl.update t.lmoved l ~f:(function
      | None -> Id.Set.singleton id
      | Some s -> Set.add s id)

(* Update when we union two nodes together. *)
let merge ({isrc = p; _} as t) a b =
  if a <> b then match Hashtbl.(find p a, find p b) with
    | None, None -> ()
    | None, Some pb -> Hashtbl.set p ~key:a ~data:pb
    | Some pa, None -> Hashtbl.set p ~key:b ~data:pa
    | Some pa, Some pb when Label.(pa = pb) -> ()
    | Some pa, Some pb when dominates t ~parent:pb pa ->
      Hashtbl.set p ~key:a ~data:pb
    | Some pa, Some pb when dominates t ~parent:pa pb ->
      Hashtbl.set p ~key:b ~data:pa
    | Some pa, Some pb ->
      let pc = lca t pa pb in
      let c = find t a in
      Hashtbl.remove p a;
      Hashtbl.remove p b;
      assert (c = find t b);
      move t [pa; pb] pc c

let check_moved t id a =
  let id = find t id in
  Hashtbl.change t.imoved id ~f:(function
      | Some s -> Some (Set.add s a)
      | None ->
        Hashtbl.set t.isrc ~key:id ~data:a;
        None)

(* We've matched on a value that we already hash-consed, so
   figure out which label it should correspond to. *)
let duplicate t id a = match Hashtbl.find t.isrc id with
  | None -> check_moved t id a
  | Some b when Label.(b = a) -> ()
  | Some b when dominates t ~parent:b a -> ()
  | Some b when dominates t ~parent:a b ->
    Hashtbl.set t.isrc ~key:id ~data:a
  | Some b ->
    let c = lca t a b in
    Hashtbl.remove t.isrc id;
    move t [a; b] c @@ find t id

module Licm = struct
  let find_loop t l = match Resolver.resolve t.input.reso l with
    | Some (`blk b | `insn (_, b, _)) ->
      Loops.blk t.input.loop @@ Blk.label b
    | None -> assert false

  let is_arg t x =
    Func.args t.input.fn |> Seq.exists ~f:(fun (y, _) -> Var.(x = y))

  let is_slot t x =
    Func.slots t.input.fn |> Seq.exists ~f:(Fn.flip Slot.is_var x)

  let is_arg_or_slot t x = is_arg t x || is_slot t x

  let is_child_loop t a b =
    not (Loops.equal_loop a b) &&
    Loops.is_child_of t.input.loop a b

  let id2label t id = match Hashtbl.find t.isrc id with
    | None -> Hashtbl.find t.idest id
    | Some _ as l -> l

  module Variance = struct
    let rec is_variant ~lp t l n = match find_loop t l with
      | Some lp' when is_child_loop t lp lp' -> false
      | Some _ -> children ~lp t n
      | None -> false

    and children ~lp t n = match (n : enode) with
      | N (_, cs) -> List.exists cs ~f:(child ~lp t)
      | U {pre; post} ->
        let id = find t pre in
        assert (id = find t post);
        children ~lp t @@ node t id

    (* If the child node has a known label, then recursively ask if it
       is variant w.r.t. the current loop. *)
    and child ~lp t id =
      let n = node t id in
      match id2label t id with
      | Some l -> is_variant ~lp t l n
      | None -> match n with
        | N (Ovar x, []) ->
          (* Arguments and stack slots have scope for the entire
             function. *)
          not (is_arg_or_slot t x) &&
          (* If this is a block argument, then find out if it belongs to
             a loop. *)
          Resolver.blk_arg t.input.reso x |>
          Option.value_map ~default:true ~f:(fun l -> match find_loop t l with
              | Some lp' when is_child_loop t lp lp' -> false
              | Some _ | None -> true)
        | _ ->
          (* At this point, anything that is not a constant is suspect. *)
          not @@ Enode.is_const n
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
    | Some l' -> match find_loop t l' with
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
  | Some `insn (i, _, _) when is_effectful t n i ->
    Hashtbl.set t.isrc ~key:id ~data:l
  | Some `insn _ -> match Licm.find_loop t l with
    | None -> Hashtbl.set t.isrc ~key:id ~data:l
    | Some lp -> Licm.licm t l n lp id
