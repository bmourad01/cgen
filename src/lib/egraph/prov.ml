(* Track the provenance between e-class IDs and labels in the CFG
   representation. *)

open Core
open Graphlib.Std
open Common

(* Lowest common ancestor in the dominator tree. *)
let rec lca t a b =
  let p = Tree.parent t.input.cdom in
  match p a, p b with
  | Some a, Some b when Label.(a = b) -> a
  | Some a, Some b -> lca t a b
  | None, _ | _, None ->
    (* The root is pseudoentry, which we should never reach. *)
    assert false

let move t a b c id =
  Hashtbl.remove t.id2lbl id;
  Hashtbl.update t.imoved id ~f:(function
      | None -> Label.Set.of_list [a; b]
      | Some s -> Set.(add (add s a) b));
  Hashtbl.update t.lmoved c ~f:(function
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
      move t pa pb pc c

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
    move t a b c @@ find t id
