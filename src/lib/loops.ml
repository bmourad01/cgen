open Core
open Regular.Std
open Graphlib.Std
open Monads.Std

module O = Monad.Option

let rec while_top q ~f = match Stack.top q with
  | Some x -> f x; while_top q ~f
  | None -> ()

module Make(Cfg : Label.Graph_s) : Loops_intf.S with type cfg := Cfg.t = struct
  open O.Let

  type loop = int [@@deriving compare, equal]
  type level = int [@@deriving compare, equal]

  let pp_loop = Int.pp
  let pp_level = Int.pp

  type data = {
    ident          : loop;
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
      "((ident %a) (header %a) (parent %a) (level %a))"
      pp_loop d.ident
      Label.pp d.header
      (Format.pp_print_option ~none pp_loop) d.parent
      pp_level d.level

  let create_data i l = {
    ident = i;
    header = l;
    parent = None;
    level = -1;
  }

  type t = {
    name  : string;
    loops : data Vec.t;
    blks  : loop Label.Table.t;
  }

  let pp ppf t =
    let pp_sep ppf () = Format.fprintf ppf " " in
    let pp_blk ppf (blk, lp) = Format.fprintf ppf "(%a %a)" Label.pp blk pp_loop lp in
    Format.fprintf ppf
      "((name %s) (loops (%a)) (blks (%a))"
      t.name
      (Format.pp_print_list ~pp_sep pp_data) (Vec.to_list t.loops)
      (Format.pp_print_list ~pp_sep pp_blk) (Hashtbl.to_alist t.blks)

  let init name = {
    name;
    loops = Vec.create ();
    blks = Label.Table.create ();
  }

  let get t n = match Vec.get t.loops n with
    | Some d -> d
    | None ->
      invalid_argf
        "Loop %d does not exist in function $%s"
        n t.name ()

  let blk t l = Hashtbl.find t.blks l
  let mem t l = Hashtbl.mem t.blks l

  let is_header t l = match blk t l with
    | Some n -> Label.equal l @@ (get t n).header
    | None -> false

  let rec is_child_of ~parent t n =
    n = parent || match (get t n).parent with
    | Some p -> is_child_of ~parent t p
    | None -> false

  let is_in_loop t l n = match blk t l with
    | Some m -> is_child_of ~parent:n t m
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
    Vec.push t.loops @@ create_data n l;
    n

  let dom_backedge l cfg dom =
    Cfg.Node.preds l cfg |> Seq.filter
      ~f:(Semi_nca.Tree.dominates dom l)

  (* Discover loop headers and initialize all candidate blocks in reverse postorder.

     A loop header is a block that dominates one of its back-edges.
  *)
  let find_headers t cfg dom =
    Graphlib.reverse_postorder_traverse (module Cfg)
      ~start:Label.pseudoentry cfg |> Seq.iter ~f:(fun l ->
          if dom_backedge l cfg dom |> Seq.is_empty |> not then
            Hashtbl.set t.blks ~key:l ~data:(new_loop t l))

  (* Check if loop `m` can be reparented under loop `n`. If so, return the root of `m`. *)
  let find_candidate_for_reparenting t n m =
    let rec chase m = function
      | None -> Some m
      | Some p when n = p -> None
      | Some p -> chase p (get t p).parent in
    let* m = chase m (get t m).parent in
    Option.some_if (n <> m) m

  let visit_loop_block t n l = match Hashtbl.find t.blks l with
    | None ->
      (* We haven't visited this block yet, so it needs to be
         enqueued for analysis. *)
      Hashtbl.set t.blks ~key:l ~data:n;
      Some l
    | Some m ->
      let+ m = find_candidate_for_reparenting t n m in
      let d = get t m in
      d.parent <- Some n;
      d.header

  (* Work to collect all blocks in a given loop by walking backwards from
     all of its back-edges. *)
  let analyze_loop t cfg q n =
    Stack.until_empty q @@ fun l -> match visit_loop_block t n l with
    | Some c -> Cfg.Node.preds c cfg |> Seq.iter ~f:(Stack.push q)
    | None -> ()

  let find_loop_blks t cfg dom =
    let q = Stack.create () in
    (* We need to traverse the loops in pseudo-postorder. *)
    Vec.iteri_rev t.loops ~f:(fun n lp ->
        (* Enqueue the predecessors that the loop header dominates. *)
        dom_backedge lp.header cfg dom |>
        Seq.iter ~f:(Stack.push q);
        analyze_loop t cfg q n)

  let set_level q d k =
    d.level <- k;
    ignore @@ Stack.pop_exn q

  let assign_loop_level t q d = match d.parent with
    | None -> set_level q d 0
    | Some p -> match (get t p).level with
      | k when k < 0 -> Stack.push q p
      | k -> set_level q d (k + 1)

  let assign_levels t =
    let q = Stack.create () in
    Vec.iteri t.loops ~f:(fun n d ->
        if d.level < 0 then begin
          Stack.push q n;
          while_top q ~f:(fun n -> assign_loop_level t q @@ get t n);
        end)

  let analyze ?dom ~name cfg =
    let t = init name in
    let dom = match dom with
      | Some dom -> dom
      | None -> Semi_nca.compute (module Cfg) cfg Label.pseudoentry in
    find_headers t cfg dom;
    find_loop_blks t cfg dom;
    assign_levels t;
    t
end
