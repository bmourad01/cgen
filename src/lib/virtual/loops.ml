open Core
open Regular.Std
open Graphlib.Std

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

let chase_parent t n m =
  let rec parent m = function
    | None -> Some m
    | Some p when p = n -> None
    | Some p -> parent p (get t p).parent in
  parent m (get t m).parent

let find_next t n l = match Hashtbl.find t.blks l with
  | None ->
    Hashtbl.set t.blks ~key:l ~data:n;
    Some l
  | Some m -> match chase_parent t n m with
    | None -> None
    | Some m when n = m -> None
    | Some m ->
      let d = get t m in
      d.parent <- Some n;
      Some d.header

let find_loop_blks t cfg dom =
  let q = Stack.create () in
  Vec.to_sequence_rev_mutable t.loops |>
  Seq.iteri ~f:(fun n d ->
      dom_backedge d.header cfg dom |>
      Seq.iter ~f:(Stack.push q);
      while not @@ Stack.is_empty q do
        Stack.pop_exn q |>
        find_next t n |> 
        Option.iter ~f:(fun c ->
            Cfg.Node.preds c cfg |>
            Seq.iter ~f:(Stack.push q))
      done)

let assign_levels t =
  let q = Stack.create () in
  let set d n =
    d.level <- n;
    ignore @@ Stack.pop_exn q in
  Vec.to_sequence_mutable t.loops |>
  Seq.iteri ~f:(fun n d ->
      if d.level < 0 then begin
        Stack.push q n;
        while not @@ Stack.is_empty q do
          let n = Stack.top_exn q in
          let d = get t n in
          match d.parent with
          | None -> set d 0
          | Some p -> match (get t p).level with
            | k when k < 0 -> Stack.push q p
            | k -> set d (k + 1)
        done
      end)

let analyze fn =
  let t = init () in
  let cfg = Cfg.create fn in
  let dom = Graphlib.dominators (module Cfg) cfg Label.pseudoentry in
  find_headers t cfg dom;
  find_loop_blks t cfg dom;
  assign_levels t;
  t
