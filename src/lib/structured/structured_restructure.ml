open Core
open Regular.Std
open Graphlib.Std
open Virtual

module Ltree = Label.Tree
module Stmt = Structured_stmt

type blks = blk Ltree.t

type t = {
  fn   : func;
  tenv : Typecheck.env;
  blks : blks;
  cfg  : Cfg.t;
  scc  : Label.t partition;
  dom  : Label.t Semi_nca.tree;
  rpo  : Label.t -> int;
}

let init ~tenv fn =
  let cfg = Cfg.create fn in
  let blks = Func.map_of_blks fn in
  let scc = Graphlib.strong_components (module Cfg) cfg in
  let dom = Semi_nca.compute (module Cfg) cfg Label.pseudoentry in
  let rpo =
    let t = Label.Table.create () in
    Graphlib.reverse_postorder_traverse (module Cfg) cfg |>
    Seq.iteri ~f:(fun i key -> Hashtbl.set t ~key ~data:i);
    Hashtbl.find_exn t in
  {fn; tenv; blks; cfg; scc; dom; rpo}

let is_backward t ~src ~dst = t.rpo dst <= t.rpo src

let dominates t u v =
  Label.(u = v) || Semi_nca.Tree.is_descendant_of t.dom ~parent:u v

let is_merge t n =
  Cfg.Node.preds n t.cfg |>
  Seq.count ~f:(fun p -> not @@ is_backward t ~src:p ~dst:n) |>
  fun c -> c > 1

let is_loop_header t n =
  Cfg.Node.preds n t.cfg |> Seq.exists ~f:(dominates t n)

type frame =
  | Loop of Label.t
  | Join of Label.t

type ctx = {
  frames : frame list;
} [@@unboxed]

let empty_ctx = {
  frames = [];
}

let push_loop h ctx = {frames = Loop h :: ctx.frames}
let push_join j ctx = {frames = Join j :: ctx.frames}
let in_frames ctx ~f = List.exists ctx.frames ~f

let equal_loop n = function
  | Loop h -> Label.(h = n)
  | Join _ -> false

let equal_join n = function
  | Join j -> Label.(j = n)
  | Loop _ -> false

let emit_body t n =
  let b = Ltree.find_exn t.blks n in
  Blk.insns b |> Seq.map ~f:(fun i ->
      (Insn.op i :> Stmt.t)) |>
  Seq.to_list |> Stmt.seq

let of_dst : dst -> Stmt.goto = function
  | #global as g -> g
  | `label (l, _) -> `label l

let emit_raw_term t n : Stmt.t =
  let b = Ltree.find_exn t.blks n in
  match Blk.ctrl b with
  | `jmp d -> `goto (of_dst d)
  | `br (c, y, n) ->
    `ite (`var c, `goto (of_dst y), `goto (of_dst n))
  | `sw (ty, i, `label (d, _), tbl) ->
    let cs =
      Ctrl.Table.enum tbl |>
      Seq.map ~f:(fun (i, `label (l, _)) ->
          `case (i, `goto (`label l))) |> Seq.to_list in
    let d = `default (`goto (`label d)) in
    `sw (i, ty, cs @ [d])
  | `ret _ as r -> r
  | `hlt -> `hlt

let emit_goto_island t g =
  Group.enum g |> Seq.map ~f:(fun n ->
      let body = emit_body t n in
      let term = emit_raw_term t n in
      `label (n, `seq (body, term))) |>
  Seq.to_list |> Stmt.seq

type state = {
  scheduled : Label.Hash_set.t;
  pending   : Label.t Vec.t;
}

let init_state () = {
  scheduled = Label.Hash_set.create ();
  pending = Vec.create ();
}

let is_multi_entry_scc t g =
  Group.enum g |> Seq.count ~f:(fun v ->
      Cfg.Node.preds v t.cfg |>
      Seq.exists ~f:(Fn.non @@ Group.mem g)) |>
  fun c -> c > 1

type jump_kind =
  | Fallthrough
  | Continue
  | Break
  | Inline
  | Shared
  | Goto

let region_root t ctx =
  match ctx.frames with
  | Loop h :: _ -> h
  | Join j :: _ -> j
  | _ -> Func.entry t.fn

let preds_in_region t n ~ctx =
  let root = region_root t ctx in
  Cfg.Node.preds n t.cfg |>
  Seq.count ~f:(fun p ->
      not (is_backward t ~src:p ~dst:n) &&
      dominates t root p)

let outside_current_loop t n ~ctx =
  match ctx.frames with
  | Loop h :: _ ->
    not (dominates t h n) ||
    Partition.group t.scc h |>
    Option.value_map ~default:false
      ~f:(fun g -> not @@ Group.mem g n)
  | _ -> false

let classify_jump t ~ctx ~src ~dst =
  (* Loop backedge -> continue *)
  let bwd = is_backward t ~src ~dst in
  if bwd && in_frames ctx ~f:(equal_loop dst) then Continue
  else if bwd && outside_current_loop t dst ~ctx then Break
  else
    (* Jumping back to the region root -> inline *)
    let root = region_root t ctx in
    if Label.(dst = root) then Inline else
      let c = preds_in_region t dst ~ctx in
      (* Shared destination *)
      if c > 1 then Shared
      (* Unique destination -> inline *)
      else if c = 1 then Inline
      (* Otherwise emit a goto. *)
      else Goto

let rec emit_branch t ~ctx ~st ~src ~dst =
  match classify_jump t ~ctx ~src ~dst with
  | Fallthrough -> `nop
  | Continue -> `continue
  | Break -> `break
  | Inline -> emit_node t dst ~ctx ~st
  | Shared ->
    Hash_set.strict_add st.scheduled dst |>
    Or_error.iter ~f:(fun () -> Vec.push st.pending dst);
    `goto (`label dst)
  | Goto -> `goto (`label dst)

and emit_dst t n dst ~ctx ~st = match dst with
  | #global as g -> `goto g
  | `label (dst, _) -> emit_branch t ~ctx ~st ~src:n ~dst

and emit_term t n ~ctx ~st =
  let b = Ltree.find_exn t.blks n in
  match Blk.ctrl b with
  | `ret _ as r -> r
  | `hlt -> `hlt
  | `jmp d -> emit_dst t n d ~ctx ~st
  | `br (c, y, n_) ->
    let y = emit_dst t n y ~ctx ~st in
    let n = emit_dst t n n_ ~ctx ~st in
    `ite (`var c, y, n)
  | `sw (ty, i, `label (d, _), tbl) ->
    let cs =
      Ctrl.Table.enum tbl |>
      Seq.map ~f:(fun (i, `label (dst, _)) ->
          let c = emit_branch t ~ctx ~st ~src:n ~dst in
          `case (i, c)) |> Seq.to_list in
    let d = `default (emit_branch t ~ctx ~st ~src:n ~dst:d) in
    `sw (i, ty, cs @ [d])

and emit_shared t ~ctx ~st =
  Vec.to_sequence_mutable st.pending |>
  Seq.map ~f:(fun l -> `label (l, emit_plain t l ~ctx ~st)) |>
  Seq.to_list |> Stmt.seq

and emit_loop t n ~ctx ~st =
  let st = init_state () in
  let ctx = push_loop n ctx in
  let body = emit_plain t n ~ctx ~st in
  let shared = emit_shared t ~ctx ~st in
  `loop (`seq (body, shared))

and emit_plain t n ~ctx ~st =
  let body = emit_body t n in
  let term = emit_term t n ~ctx ~st in
  `seq (body, term)

and emit_node t n ~ctx ~st =
  if is_loop_header t n then emit_loop t n ~ctx ~st
  else emit_plain t n ~ctx ~st

let run ~tenv fn =
  let t = init ~tenv fn in
  let st = init_state () in
  let ctx = empty_ctx in
  let body = emit_node t (Func.entry fn) ~ctx ~st in
  let shared = emit_shared t ~ctx ~st in
  let body = Stmt.normalize @@ `seq (body, shared) in
  Structured_func.create () ~body
    ~dict:(Func.dict fn)
    ~name:(Func.name fn)
    ~args:(Seq.to_list @@ Func.args fn)
    ~slots:(Seq.to_list @@ Func.slots fn)
