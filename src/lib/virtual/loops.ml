open Core
open Regular.Std
open Graphlib.Std
open Monads.Std

module O = Monad.Option

open O.Let

type loop = int [@@deriving compare, equal]
type level = int [@@deriving compare, equal]

let pp_loop = Int.pp
let pp_level = Int.pp

type data = {
  header         : Label.t;
  mutable parent : loop option;
  mutable level  : level;
}

let header d = d.header
let parent d = d.parent
let level d = d.level

let pp_data ppf d =
  let none ppf () = Format.fprintf ppf "none" in
  Format.fprintf ppf
    "((header %a) (parent %a) (level %a))"
    Label.pp d.header
    (Format.pp_print_option ~none pp_loop) d.parent
    pp_level d.level

let create_data l = {
  header = l;
  parent = None;
  level = -1;
}

type t = {
  loops : data Vec.t;
  blks  : loop Label.Table.t;
}

let init () = {
  loops = Vec.create ();
  blks = Label.Table.create ();
}

let get t n = Vec.get_exn t.loops n
let blk t l = Hashtbl.find t.blks l
let mem t l = Hashtbl.mem t.blks l

let is_header t l = match blk t l with
  | Some n -> Label.equal l @@ (get t n).header
  | None -> false

let rec is_child_of t n m =
  n = m || match (get t n).parent with
  | Some p -> is_child_of t p m
  | None -> false

let is_in_loop t l n = match blk t l with
  | Some m -> is_child_of t m n
  | None -> false

let loops_of t l = match blk t l with
  | None -> Seq.empty
  | Some n ->
    let open Seq.Generator in
    let rec parent n =
      yield n >>= fun () ->
      match (get t n).parent with
      | None -> return ()
      | Some n -> parent n in
    run @@ parent n

let new_loop t l =
  let n = Vec.length t.loops in
  Vec.push t.loops @@ create_data l;
  n

let dom_backedge l cfg dom =
  Cfg.Node.preds l cfg |>
  Seq.filter ~f:(Tree.is_descendant_of dom ~parent:l)

let find_headers t cfg dom =
  Graphlib.reverse_postorder_traverse (module Cfg)
    ~start:Label.pseudoentry cfg |> Seq.iter ~f:(fun l ->
        if dom_backedge l cfg dom |> Seq.is_empty |> not then
          Hashtbl.set t.blks ~key:l ~data:(new_loop t l))

(* For our analysis of the loop `n` we have a block associated
   with loop `m`. We need to recursively chase the parent of `m`
   until we reach `n` or we find no parent. *)
let chase_parent t n m =
  let rec chase m = function
    | None -> Some m
    | Some p when n = p -> None
    | Some p -> chase p (get t p).parent in
  chase m (get t m).parent

let find_next t n l = match Hashtbl.find t.blks l with
  | None ->
    (* We haven't visited this block yet, so it needs to be
       enqueued for analysis. *)
    Hashtbl.set t.blks ~key:l ~data:n;
    Some l
  | Some m ->
    (* We found that `m` has no parent. *)
    let* m = chase_parent t n m in
    (* Check to see if it's the loop we're analyzing. *)
    let+ () = O.guard (n <> m) in
    (* Set the parent. *)
    let d = get t m in
    d.parent <- Some n;
    d.header

let analyze_loop t cfg q n =
  Stack.until_empty q @@ fun l -> match find_next t n l with
  | Some c -> Cfg.Node.preds c cfg |> Seq.iter ~f:(Stack.push q)
  | None -> ()

let find_loop_blks t cfg dom =
  let q = Stack.create () in
  (* We need to traverse the loops in pseudo-postorder. *)
  Vec.iteri_rev t.loops ~f:(fun n lp ->
      (* Enqueue the predecessors that the loop header dominates. *)
      dom_backedge lp.header cfg dom |>
      Seq.iter ~f:(Stack.push q);
      (* Analyze the loop. *)
      analyze_loop t cfg q n)

let set_level q d k =
  d.level <- k;
  ignore @@ Stack.pop_exn q

let loop_level t q d = match d.parent with
  | None ->  set_level q d 0
  | Some p -> match (get t p).level with
    | k when k < 0 -> Stack.push q p
    | k -> set_level q d (k + 1)

let rec assign_loop t q = match Stack.top q with
  | None -> ()
  | Some n ->
    loop_level t q @@ get t n;
    assign_loop t q

let assign_levels t =
  let q = Stack.create () in
  Vec.iteri t.loops ~f:(fun n d ->
      if d.level < 0 then begin
        Stack.push q n;
        assign_loop t q
      end)

let analyze fn =
  let t = init () in
  let cfg = Cfg.create fn in
  let dom = Graphlib.dominators (module Cfg) cfg Label.pseudoentry in
  find_headers t cfg dom;
  find_loop_blks t cfg dom;
  assign_levels t;
  t
