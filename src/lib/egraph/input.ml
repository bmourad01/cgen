open Core
open Monads.Std
open Regular.Std
open Graphlib.Std
open Virtual

exception Occurs_failed of Var.t * Label.t option

module E = Monad.Result.Error
module G = Graphlib.Make(Label)(Unit)

open E.Let

type resolved = [
  | `blk  of blk
  | `insn of insn * blk * Var.t option
]

(* General information about the function we're translating. *)
type t = {
  fn  : func;
  tbl : resolved Label.Table.t;
  cfg : Cfg.t;
  dom : Label.t tree;
}

module Pseudo = struct
  let connect_with_entry n =
    let e = Label.pseudoentry in
    if Label.(n = e) then Fn.id
    else G.Edge.(insert (create e n ()))

  let connect_with_exit n =
    let e = Label.pseudoexit in
    if Label.(n = e) then Fn.id
    else G.Edge.(insert (create n e ()))

  let if_unreachable ~from connect g n =
    if G.Node.degree ~dir:from n g = 0 then connect n else Fn.id

  let connect_unreachable g n =
    if_unreachable ~from:`Out connect_with_exit  g n @@
    if_unreachable ~from:`In  connect_with_entry g n @@
    g

  let add g =
    G.nodes g |> Seq.fold ~init:g ~f:connect_unreachable |> fun g ->
    Graphlib.depth_first_search (module G) g
      ~init:g ~start:Label.pseudoentry
      ~start_tree:connect_with_entry |> fun g ->
    Graphlib.depth_first_search (module G) g
      ~rev:true ~init:g ~start:Label.pseudoexit
      ~start_tree:connect_with_exit
end

let create_tbl fn =
  let input = Label.Table.create () in
  let+ () = Func.blks fn |> E.Seq.iter ~f:(fun b ->
      let label = Blk.label b in
      let* () = match Hashtbl.add input ~key:label ~data:(`blk b) with
        | `Ok -> Ok ()
        | `Duplicate ->
          E.failf "Duplicate label for block %a" Label.pp label () in
      Blk.insns b |> E.Seq.iter ~f:(fun i ->
          let key = Insn.label i in
          let data = `insn (i, b, Insn.lhs i) in
          match Hashtbl.add input ~key ~data with
          | `Ok -> Ok ()
          | `Duplicate ->
            E.failf "Duplicate label for instruction %a in block %a"
              Label.pp key Label.pp label ())) in
  input

(* The "regular" dominator tree from the CFG is not fine-grained enough
   to work with our strategy for maintaining provenance in the e-graph.

   The tree should also include labels of instructions when considering
   the data-flow of the function.
*)
let doms fn tbl cfg =
  let d = Graphlib.dominators (module Cfg) cfg Label.pseudoentry in
  let accum b g l =
    Blk.insns ~rev:true b |> Seq.fold ~init:(g, l) ~f:(fun (g, l) i ->
        let next = Insn.label i in
        let e = G.Edge.create next l () in
        G.Edge.insert e g, next) in 
  let rec aux g l = match Hashtbl.find tbl l with
    | None when Label.is_pseudo l -> g, l
    | None | Some (`insn _) -> assert false
    | Some (`blk b) ->
      let g, first = accum b g l in
      children g l, first
  and children g l =
    Tree.children d l |> Seq.fold ~init:g ~f:(fun g c ->
        let g, first = aux g c in
        let e = G.Edge.create l first () in
        G.Edge.insert e g) in
  let entry = Func.entry fn in
  let g = fst @@ aux (G.Node.insert entry G.empty) entry in
  Graphlib.dominators (module G) (Pseudo.add g) Label.pseudoentry  

let init fn =
  let+ tbl = create_tbl fn in
  let cfg = Cfg.create fn in
  let dom = doms fn tbl cfg in
  {fn; tbl; cfg; dom}

(* Builds the expression trees from the CFG representation. *)
module Builder = struct
  open Exp

  (* The state of the expression builder. *)
  type t = {
    pure   : Exp.pure Var.Table.t;
    exp    : Exp.t Label.Table.t;
    filled : Var.Hash_set.t;
  }

  let init () = {
    pure = Var.Table.create ();
    exp = Label.Table.create ();
    filled = Var.Hash_set.create ();
  }

  (* The worklist keeps track of the dependencies that the algorithm
     should attempt to resolve. *)
  module Worklist = struct
    type t = Label.Set.t Var.Map.t

    let empty = Var.Map.empty
    let is_empty = Map.is_empty
    let remove = Map.remove
    let mem = Map.mem

    let singleton x l =
      Var.Map.singleton x @@ Label.Set.singleton l

    let add w x l = Map.update w x ~f:(function
        | None -> Label.Set.singleton l
        | Some s -> Set.add s l)
  end

  (* Each pure expression in the table starts out with free variables
     for any dependencies. We want to saturate each of these with
     subexpressions by substituting these free variables. *)
  module Subst = struct
    (* Keep track of the set of variables we're substituting. If
       we find a cycle in the dependency chain then the function
       is probably not in SSA form. *)
    let rec pure ?(vs = Var.Set.empty) t e =
      let go = pure t ~vs in match e with
      | Palloc _ as a -> a
      | Pbinop (l, o, x, y) ->
        Pbinop (l, o, go x, go y)
      | Pbool _ | Pdouble _ | Pint _ | Psingle _ | Psym _ -> e
      | Pcall (l, ty, f, args, vargs) ->
        let args = List.map args ~f:go in
        let vargs = List.map vargs ~f:go in
        Pcall (l, ty, global t f ~vs, args, vargs)
      | Pload (l, t, a) -> Pload (l, t, go a)
      | Psel (l, t, c, y, n) -> Psel (l, t, go c, go y, go n)
      | Punop (l, o, x) -> Punop (l, o, go x)
      | Pvar x when Set.mem vs x -> raise @@ Occurs_failed (x, None)
      | Pvar x as default ->
        Hashtbl.find t.pure x |>
        Option.value_map ~default ~f:(continue x vs t)

    (* Make the full substitution on subterms and cache the results. *)
    and continue x vs t = function
      | (Palloc _ | Pbool _ | Pdouble _ | Pint _ | Psingle _ | Psym _) as e -> e
      | e when Hash_set.mem t.filled x -> e
      | e ->
        let e = pure t e ~vs:(Set.add vs x) in
        Hashtbl.set t.pure ~key:x ~data:e;
        Hash_set.add t.filled x;
        e

    and global ?(vs = Var.Set.empty) t = function
      | (Gaddr _ | Gsym _) as g -> g
      | Gpure p -> Gpure (pure t p ~vs)

    let local t (l, args) = l, List.map args ~f:(pure t)

    let dst t = function
      | Dglobal g -> Dglobal (global t g)
      | Dlocal l -> Dlocal (local t l)

    let table m = List.map ~f:(fun (i, l) -> i, local m l)

    let exp t = function
      | Ebr (c, y, n) -> Ebr (pure t c, dst t y, dst t n)
      | Ecall (f, args, vargs) ->
        let args = List.map args ~f:(pure t) in
        let vargs = List.map vargs ~f:(pure t) in
        Ecall (global t f, args, vargs)
      | Ejmp d -> Ejmp (dst t d)
      | Eret p -> Eret (pure t p)
      | Eset (x, y) -> Eset (x, pure t y ~vs:(Var.Set.singleton x))
      | Estore (ty, v, a) -> Estore (ty, pure t v, pure t a)
      | Esw (ty, v, d, tbl) ->
        Esw (ty, pure t v, local t d, table t tbl)
  end

  let operand (o : operand) w l = match o with
    | `bool f     -> Pbool f, w
    | `int (i, t) -> Pint (i, t), w
    | `float f    -> Psingle f, w
    | `double d   -> Pdouble d, w
    | `sym (s, o) -> Psym (s, o), w
    | `var v      -> Pvar v, Worklist.add w v l

  let operands os w l =
    List.fold_right os ~init:([], w) ~f:(fun o (os, w) ->
        let o, w = operand o w l in
        o :: os, w)

  let global (g : Virtual.global) w l = match g with
    | `addr a -> Gaddr a, w
    | `sym s  -> Gsym s, w
    | `var v  -> Gpure (Pvar v), Worklist.add w v l

  let local (loc : Virtual.local) w l = match loc with
    | `label (lbl, args) ->
      let args, w = operands args w l in
      (lbl, args), w

  let dst (d : Virtual.dst) w l = match d with
    | #Virtual.global as g ->
      let g, w = global g w l in
      Dglobal g, w
    | #Virtual.local as loc ->
      let loc, w = local loc w l in
      Dlocal loc, w

  let table tbl w l =
    let tbl, w =
      Ctrl.Table.enum tbl |>
      Seq.fold ~init:([], w) ~f:(fun (tbl, w) (i, loc) ->
          let loc, w = local loc w l in
          (i, loc) :: tbl, w) in
    List.rev tbl, w

  let update t l ((w, xs) as acc) x f =
    (* Fail if we've already seen this variable. *)
    if Set.mem xs x then
      raise @@ Occurs_failed (x, Some l);
    if Worklist.mem w x then
      let w' = ref @@ Worklist.remove w x in
      (* Assume that the current bound expression is the same. *)
      if not @@ Hashtbl.mem t.pure x then begin
        let w, p = f !w' in
        (* Fail early if we re-introduce the same variable. *)
        if Worklist.mem w x then
          raise @@ Occurs_failed (x, Some l);
        Hashtbl.set t.pure ~key:x ~data:p;
        w' := w;
      end;
      !w', Set.add xs x
    else acc

  (* Accumulate the results of an instruction. *)
  let accum t acc i =
    let l = Insn.label i in
    let go = update t l acc in
    match Insn.op i with
    | `bop (x, o, a, b) -> go x @@ fun w ->
      let a, w = operand a w l in
      let b, w = operand b w l in
      w, Pbinop (Some l, o, a, b)
    | `uop (x, o, a) -> go x @@ fun w ->
      let a, w = operand a w l in
      w, Punop (Some l, o, a)
    | `sel (x, t, c, y, n) -> go x @@ fun w ->
      let c, w = Pvar c, Worklist.add w c l in
      let y, w = operand y w l in
      let n, w = operand n w l in
      w, Psel (Some l, t, c, y, n)
    | `call (None, _, _, _) -> acc
    | `call (Some (x, t), f, args, vargs) -> go x @@ fun w ->
      let f, w = global f w l in
      let args, w = operands args w l in
      let vargs, w = operands vargs w l in
      w, Pcall (Some l, t, f, args, vargs)
    | `alloc (x, n) -> go x @@ fun w -> w, Palloc (Some l, n)
    | `load (x, t, a) -> go x @@ fun w ->
      let a, w = operand a w l in
      w, Pload (Some l, t, a)
    | `store _ -> acc
    | `vaarg (x, _, y) ->
      let w, xs = acc in
      let w = Worklist.remove w x in
      let w = Worklist.remove w y in
      w, xs
    | `vastart x ->
      let w, xs = acc in
      Worklist.remove w x, xs

  (* Kill the variables that appear in the arguments of the block.
     This is the point where we can no longer represent their data
     dependencies as an expression tree.

     Note that this could be a result of a "diamond" property in
     the CFG, not necessarily a loop.
  *)
  let killed blk w =
    Blk.args blk |> Seq.map ~f:fst |>
    Seq.fold ~init:w ~f:Worklist.remove

  let different_insn l i = Label.(l <> Insn.label i)

  let subseq blk l ss =
    if Label.(l <> Blk.label blk) then
      Seq.drop_while_option ss ~f:(different_insn l) |>
      Option.value_map ~default:Seq.empty ~f:snd
    else ss

  let insns t blk l w xs =
    let w, xs =
      Blk.insns blk ~rev:true |> subseq blk l |>
      Seq.fold ~init:(w, xs) ~f:(accum t) in
    killed blk w, xs

  (* Next blocks to visit. *)
  let nexts input blk bs =
    Cfg.Node.preds (Blk.label blk) input.cfg |>
    Seq.filter_map ~f:(fun l ->
        if Label.is_pseudo l || Set.mem bs l
        then None else match Hashtbl.find input.tbl l with
          | Some `blk b -> Some b
          | Some _ | None -> None)

  let initq blk l w =
    blk, l, w, Label.Set.empty, Var.Set.empty

  (* Traverse the data dependencies. *)
  let traverse t input blk l w =
    if not @@ Worklist.is_empty w then
      let q = Stack.singleton @@ initq blk l w in
      while not @@ Stack.is_empty q do
        let blk, l, w, bs, xs = Stack.pop_exn q in
        let w, xs = insns t blk l w xs in
        if not @@ Worklist.is_empty w then
          let bs = Set.add bs @@ Blk.label blk in
          nexts input blk bs |> Seq.iter ~f:(fun blk ->
              Stack.push q (blk, Blk.label blk, w, bs, xs))
      done

  let run t input blk l f =
    let w, e = f () in
    traverse t input blk l w;
    let e = Subst.exp t e in
    Hashtbl.set t.exp ~key:l ~data:e

  let ctrl t input blk =
    let l = Blk.label blk in
    let go = run t input blk l in
    match Blk.ctrl blk with
    | `hlt -> ()
    | `jmp d -> go @@ fun () ->
      let d, w = dst d Worklist.empty l in
      w, Ejmp d
    | `br (c, y, n) -> go @@ fun () ->
      let c, w = Pvar c, Worklist.singleton c l in
      let y, w = dst y w l in
      let n, w = dst n w l in
      w, Ebr (c, y, n)
    | `ret None -> ()
    | `ret (Some x) -> go @@ fun () ->
      let x, w = operand x Worklist.empty l in
      w, Eret x
    | `sw (t, v, d, tbl) -> go @@ fun () ->
      let v, w = match v with
        | `var x -> Pvar x, Worklist.singleton x l
        | `sym (s, n) -> Psym (s, n), Worklist.empty in
      let d, w = local d w l in
      let tbl, w = table tbl w l in
      w, Esw (t, v, d, tbl)

  let insn t input i blk =
    let l = Insn.label i in
    let go = run t input blk l in
    match Insn.op i with
    | `bop (x, o, a, b) -> go @@ fun () ->
      let a, w = operand a Worklist.empty l in
      let b, w = operand b w l in
      w, Eset (x, Pbinop (Some l, o, a, b))
    | `uop (x, o, a) -> go @@ fun () ->
      let a, w = operand a Worklist.empty l in
      w, Eset (x, Punop (Some l, o, a))
    | `sel (x, t, c, y, n) -> go @@ fun () ->
      let y, w = operand y (Worklist.singleton c l) l in
      let n, w = operand n w l in
      w, Eset (x, Psel (Some l, t, Pvar c, y, n))
    | `call (Some (x, t), f, args, vargs) -> go @@ fun () ->
      let f, w = global f Worklist.empty l in
      let args, w = operands args w l in
      let vargs, w = operands vargs w l in
      w, Eset (x, Pcall (Some l, t, f, args, vargs))
    | `alloc (x, n) -> go @@ fun () ->
      Worklist.empty, Eset (x, Palloc (Some l, n))
    | `load (x, t, a) -> go @@ fun () ->
      let a, w = operand a Worklist.empty l in
      w, Eset (x, Pload (Some l, t, a))
    | `call (None, f, args, vargs) -> go @@ fun () ->
      let f, w = global f Worklist.empty l in
      let args, w = operands args w l in
      let vargs, w = operands vargs w l in
      w, Ecall (f, args, vargs)
    | `store (t, v, a) -> go @@ fun () ->
      let v, w = operand v Worklist.empty l in
      let a, w = operand a w l in
      w, Estore (t, v, a)
    | `vaarg _ | `vastart _ -> ()

  let try_ f = try f () with
    | Occurs_failed (x, None) ->
      E.failf "Occurs check failed for variable %a" Var.pp x ()
    | Occurs_failed (x, Some l) ->
      E.failf "Occurs check failed for variable %a at instruction %a"
        Var.pp x Label.pp l ()

  let run input = try_ @@ fun () ->
    let t = init () in
    Hashtbl.iter input.tbl ~f:(function
        | `blk b -> ctrl t input b
        | `insn (i, b, _) -> insn t input i b);
    Ok t.exp
end

(* We return the expression mapping separately because this is
   only needed to "parse" the function into the e-graph, after
   which it can be discarded. *)
let create fn =
  let* input = init fn in
  let+ exp = Builder.run input in
  input, exp
