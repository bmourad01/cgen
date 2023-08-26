(* Track the provenance between e-class IDs and labels in the CFG
   representation. *)

open Core
open Regular.Std
open Graphlib.Std
open Common
open Virtual

(* Lowest common ancestor in the dominator tree. *)
let rec lca t a b =
  let p = Tree.parent t.input.cdom in
  match p a, p b with
  | Some a, Some b when Label.(a = b) -> a
  | Some a, Some b -> lca t a b
  | None, _ | _, None ->
    (* The root is pseudoentry, which we should never reach. *)
    assert false

let move t old l id =
  let s = Label.Set.of_list old in
  Hashtbl.remove t.id2lbl id;
  Hashtbl.update t.imoved id ~f:(function
      | Some s' -> Set.union s s'
      | None -> s);
  Hashtbl.set t.imoved2 ~key:id ~data:l;
  Hashtbl.update t.lmoved l ~f:(function
      | None -> Id.Set.singleton id
      | Some s -> Set.add s id)

(* Update when we union two nodes together. *)
let merge ({id2lbl = p; _} as t) a b =
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
        Hashtbl.set t.id2lbl ~key:id ~data:a;
        None)

(* We've matched on a value that we already hash-consed, so
   figure out which label it should correspond to. *)
let duplicate t id a = match Hashtbl.find t.id2lbl id with
  | None -> check_moved t id a
  | Some b when Label.(b = a) -> ()
  | Some b when dominates t ~parent:b a -> ()
  | Some b when dominates t ~parent:a b ->
    Hashtbl.set t.id2lbl ~key:id ~data:a
  | Some b ->
    let c = lca t a b in
    Hashtbl.remove t.id2lbl id;
    move t [a; b] c @@ find t id

let is_in_loop t l = match Hashtbl.find t.input.tbl l with
  | Some (`blk b | `insn (_, b, _)) ->
    Loops.mem t.input.loop @@ Blk.label b
  | None -> assert false

let find_loop t l = match Hashtbl.find t.input.tbl l with
  | Some (`blk b | `insn (_, b, _)) ->
    Loops.blk t.input.loop @@ Blk.label b
  | None -> assert false

type loop_invariance =
  | Not_in_loop
  | Invariant
  | Variant

let is_arg t x =
  Func.args t.input.fn |> Seq.exists ~f:(fun (y, _) -> Var.(x = y))

let is_slot t x =
  Func.slots t.input.fn |> Seq.exists ~f:(Fn.flip Func.Slot.is_var x)

let is_arg_or_slot t x = is_arg t x || is_slot t x

let loop_no_label t : enode -> _ Continue_or_stop.t = function
  | N (Ovar x, []) when is_arg_or_slot t x ->
    Continue Invariant
  | n when Enode.is_const n ->
    Continue Invariant
  | _ -> Stop Variant

let rec loop_invariance ~lp t l n = match find_loop t l with
  | None -> Not_in_loop
  | Some lp' when Loops.equal_loop lp lp' ->
    loop_children ~lp t n
  | Some lp' ->
    (* See if we've broken out of the loop. *)
    if Loops.is_child_of t.input.loop lp lp'
    then Invariant else loop_children ~lp t n

and loop_children ~lp t n =
  let cs = match (n : enode) with
    | N (_, cs) -> cs
    | U {pre; post} -> [pre; post] in
  let init = Invariant and finish = Fn.id in
  List.fold_until cs ~init ~finish ~f:(fun acc id ->
      let n = node t id in
      match Hashtbl.find t.id2lbl id with
      | Some l -> loop_child ~lp acc t l n
      | None -> match Hashtbl.find t.imoved2 id with
        | None -> loop_no_label t n
        | Some l -> loop_child ~lp acc t l n)

and loop_child ~lp acc t l n = match loop_invariance ~lp t l n with
  | Not_in_loop | Invariant -> Continue acc
  | Variant -> Stop Variant

let rec licm' t l n lp id =
  let data = Loops.get t.input.loop lp in
  let hdr = Loops.header data in
  (* Get the immediate dominator of the loop header. *)
  match Tree.parent t.input.dom hdr with
  | None -> assert false
  | Some l' ->
    (* Now see if this new label is also part of a loop. *)
    match find_loop t l' with
    | None -> move t [l] l' id
    | Some lp ->
      (* Determine the loop-invariance of our node at this level. *)
      match loop_children ~lp t n with
      | Not_in_loop | Variant -> move t [l] l' id
      | Invariant -> licm' t l n lp id (* Repeat. *)

let licm t l n lp id = match loop_children ~lp t n with
  | Invariant -> licm' t l n lp id
  | Not_in_loop | Variant ->
    Hashtbl.set t.id2lbl ~key:id ~data:l

(* Track the provenance between the node and the label, but first see
   if we can do LICM (loop-invariant code motion). *)
let add t l id n = match Hashtbl.find t.input.tbl l with
  | None -> assert false
  | Some `blk _ -> Hashtbl.set t.id2lbl ~key:id ~data:l
  | Some `insn (i, _, _) when Insn.is_effectful i ->
    Hashtbl.set t.id2lbl ~key:id ~data:l
  | Some `insn _ -> match find_loop t l with
    | None -> Hashtbl.set t.id2lbl ~key:id ~data:l
    | Some lp -> licm t l n lp id
