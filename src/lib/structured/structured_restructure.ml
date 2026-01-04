(* Implementation of an algorithm to re-discover structured
   control flow from a CFG.

   Ideas are taken from the following papers:

   - "On the Capabilities of While, Repeat, and Exit Statements"
     (1973) by Peterson, Takami, and Tokura
   - "Beyond Relooper: Recursive Translation of Unstructured Control
     Flow to Structured Control Flow" (2022) by N. Ramsey

   In the case of irreducible CFGs, we will emit `goto` statements
   as needed for minimizing code duplication.
*)

open Core
open Regular.Std
open Graphlib.Std
open Virtual

module Ltree = Label.Tree
module Stmt = Structured_stmt

(* Info about the function + global state.

   [work]: the nodes that are currently in progress of being emitted
   [labl]: nodes that require a label (i.e. due to irreducible control flow)
*)
type t = {
  fn   : func;
  tenv : Typecheck.env;
  blks : blk Ltree.t;
  cfg  : cfg;
  pdom : Label.t Semi_nca.tree;
  loop : loops;
  live : live;
  work : Label.Hash_set.t;
  labl : Label.Hash_set.t;
  slot : Virtual.slot Vec.t;
}

let init ~tenv fn =
  let cfg = Cfg.create fn in
  let blks = Func.map_of_blks fn in
  let dom = Semi_nca.compute (module Cfg) cfg Label.pseudoentry in
  let loop = Loops.analyze ~dom ~name:(Func.name fn) cfg in
  let pdom = Semi_nca.compute (module Cfg) ~rev:true cfg Label.pseudoexit in
  let live = Live.compute' cfg blks in
  let work = Label.Hash_set.create () in
  let labl = Label.Hash_set.create () in
  let slot = Vec.create () in
  Func.slots fn |> Seq.iter ~f:(Vec.push slot);
  {fn; tenv; blks; cfg; pdom; loop; live; work; labl; slot}

(* Find the lowest post-dominator that is outside of the loop. *)
let loop_exit t lp =
  let rec climb j =
    if Loops.is_in_loop t.loop j lp then
      match Semi_nca.Tree.parent t.pdom j with
      | Some p -> climb p
      | None -> None
    else if Ltree.mem t.blks j then Some j
    else None in
  climb Loops.(header @@ get t.loop lp)

(* If this loop is nested, find the header of its parent. *)
let parent_loop_header t lp =
  Loops.get t.loop lp |> Loops.parent |>
  Option.map ~f:(Loops.get t.loop) |>
  Option.map ~f:Loops.header

(* A "region" that we're exploring.

   [Loop (h, lp)]: a loop [lp] with header label [h]
   [Join j]: a region with join point label [j]
   [Switch s]: same as [Join s], but specialized to a switch
*)
type frame =
  | Loop of Label.t * Loops.loop
  | Join of Label.t
  | Switch of Label.t

let pp_frame ppf = function
  | Loop (h, lp) ->
    Format.fprintf ppf "loop(%a,%a)" Label.pp h Loops.pp_loop lp
  | Join j ->
    Format.fprintf ppf "join(%a)" Label.pp j
  | Switch s ->
    Format.fprintf ppf "switch(%a)" Label.pp s
[@@ocaml.warning "-32"]

type ctx = {
  frames : frame list; (* The current stack of regions *)
} [@@unboxed]

let empty_ctx = {
  frames = [];
}

module Region = struct
  let push_loop h lp ctx = {frames = Loop (h, lp) :: ctx.frames}

  let push_switch s ctx = match ctx.frames with
    | Switch s0 :: _ when Label.(s = s0) -> ctx
    | _ -> {frames = Switch s :: ctx.frames}

  let push_join j ctx = match ctx.frames with
    | Join j0 :: _ when Label.(j = j0) -> ctx
    | _ -> {frames = Join j :: ctx.frames}

  let innermost_loop ctx =
    List.find_map ctx.frames ~f:(function
        | Loop (h, lp) -> Some (h, lp)
        | _ -> None)

  let join_is_active j ctx =
    List.exists ctx.frames ~f:(function
        | Join l | Switch l -> Label.(l = j)
        | _ -> false)
end

let possible_join t n ~ctx =
  Cfg.Node.succs n t.cfg |>
  Seq.reduce ~f:(Semi_nca.Tree.lca_exn t.pdom) |>
  Option.bind ~f:(fun j -> Option.some_if begin
      (* The join point is a valid block. *)
      Ltree.mem t.blks j &&
      (* If this join point is in any stack of loops,
         then `n` (our source node) is within all of
         them. *)
      Loops.loops_of t.loop j |>
      Seq.for_all ~f:(Loops.is_in_loop t.loop n) &&
      (* Skip if this join is an active region. *)
      not (Region.join_is_active j ctx)
    end j)

(* Classification of a jump. *)
type jmpcls =
  | Fallthrough
  | Continue
  | Break
  | Inline
[@@deriving sexp]

let pp_jmpcls ppf cls =
  Format.fprintf ppf "%a" Sexp.pp_hum @@ sexp_of_jmpcls cls
[@@ocaml.warning "-32"]

module Classify = struct
  let continue ctx ~dst =
    let rec find = function
      | Loop (h, _) :: _ ->
        (* Jumping back to current loop header. *)
        Label.(h = dst)
      | (Switch _ | Join _) :: rest ->
        (* Skip join points. *)
        find rest
      | _ -> false in
    find ctx.frames

  let break_loop t ~ctx ~dst =
    match Region.innermost_loop ctx with
    | None -> false
    | Some (h, lp) ->
      (* We're not jumping back to the current loop header. *)
      not (Loops.is_in_loop t.loop dst lp) && begin
        (* We're jumping to the exit of the current loop. *)
        Option.exists (loop_exit t lp) ~f:(Label.equal dst) ||
        (* We're jumping to our parent loop's header. *)
        Option.exists (parent_loop_header t lp) ~f:(Label.equal dst)
      end

  (* Like `fallthrough` below, but specialized for a `Switch`
     join point. *)
  let break_switch ctx ~dst = match ctx.frames with
    | Switch s :: _ -> Label.(s = dst)
    | _ -> false

  (* Jumps to nearest join point. *)
  let fallthrough ctx ~dst = match ctx.frames with
    | Join j :: _ -> Label.(j = dst)
    | _ -> false

  (* Emitting a `continue` is safe, but if a fallthrough
     is semantically valid here then we should prefer that,
     as it is a bit cleaner. *)
  let continue_or_fallthrough t ~ctx ~dst =
    let lp = Option.value_exn @@ Loops.blk t.loop dst in
    match loop_exit t lp with
    | Some j when fallthrough ctx ~dst:j -> Fallthrough
    | Some _ | None -> Continue

  let jmp t ~ctx ~src ~dst =
    if continue ctx ~dst then continue_or_fallthrough t ~ctx ~dst
    else if break_switch ctx ~dst then Break
    else if break_loop t ~ctx ~dst then Break
    else if fallthrough ctx ~dst then Fallthrough
    else Inline
end

(* See if this block has a single-use comparison that we
   can fold into the `ite` statement. *)
let find_single_use_cond t n =
  let ok x c =
    (* Same condition var. *)
    Var.(x = c) &&
    (* Not needed after this block. *)
    not (Set.mem (Live.outs t.live n) x) in
  Ltree.find t.blks n |> Option.bind ~f:(fun b ->
      match Blk.ctrl b with
      | `br (c, _, _) ->
        Blk.insns ~rev:true b |> Seq.hd |>
        Option.bind ~f:(fun i -> match Insn.op i with
            | `bop (x, (#Insn.cmp as cmp), l, r) when ok x c ->
              let label = Insn.label i in
              let k = `cmp (cmp, l, r) in
              Some (label, k)
            | _ -> None)
      | _ -> None)

type term = {
  stmt : Stmt.t;
  join : Label.t option;
}

let terminate ?join ctx stmt =
  let join = Option.bind join ~f:(fun j ->
      let active = Region.join_is_active j ctx in
      Option.some_if (not active) j) in
  {stmt; join}

module Make(C : Context_intf.S) = struct
  open C.Syntax

  let typeof_var t x =
    Typecheck.Env.typeof_var t.fn x t.tenv |>
    C.lift_err ~prefix:"Restructure"

  let layout t name =
    Typecheck.Env.layout name t.tenv |>
    C.lift_err ~prefix:"Restructure"

  module W = Windmill.Make(C)

  let windmill t l moves out =
    W.windmill t l moves ~emit:(fun dst src ->
        typeof_var t dst >>= function
        | #Type.basic as b ->
          C.return @@ Vec.push out @@ `uop (dst, `copy b, src)
        | `compound (name, _, _)
        | `opaque (name, _, _) ->
          let* lt = layout t name in
          let* s = C.Var.fresh in
          let size = Type.Layout.sizeof lt in
          let align = Type.Layout.align lt in
          let*? slot = Virtual.Slot.create s ~size ~align in
          Vec.push t.slot slot;
          C.return begin
            Vec.push out @@ `store (`name name, src, `var s);
            Vec.push out @@ `load (dst, `name name, `var s)
          end
        | `flag ->
          let+ f = C.Var.fresh in
          let zero = `int (Bv.zero, `i8) in
          Vec.push out @@ `uop (f, `flag `i8, src);
          Vec.push out @@ `bop (dst, `ne `i8, `var f, zero))

  module Emit = struct
    (* Plain sequence of instructions. *)
    let body ?k t n = match Ltree.find t.blks n with
      | Some b ->
        let s = match k with
          | None -> Blk.insns b
          | Some k -> Blk.insns b |> Seq.filter ~f:(fun i ->
              not @@ Label.equal k @@ Insn.label i) in
        Seq.map s ~f:(fun i -> (Insn.op i :> Stmt.t)) |>
        Seq.to_list |> Stmt.seq |> C.return
      | None ->
        C.failf
          "Restructure: cannot emit body for non-existent \
           block %a in function $%s" Label.pp n (Func.name t.fn) ()

    (* Branch to a block. *)
    let rec branch t ~ctx ~src ~dst =
      let cls = Classify.jmp t ~ctx ~src ~dst in
      Logs.debug (fun m ->
          m "%s: $%s:@;\
             src=%a,@;\
             dst=%a,@;\
             cls=%a,@;\
             frames=%a%!"
            __FUNCTION__ (Func.name t.fn) Label.pp src
            Label.pp dst pp_jmpcls cls
            (Format.pp_print_list
               ~pp_sep:(fun ppf () -> Format.fprintf ppf " ")
               pp_frame) ctx.frames);
      match cls with
      | Fallthrough -> !!`nop
      | Continue -> !!`continue
      | Break -> !!`break
      | Inline -> node t dst ~ctx

    (* Local control-flow destination. *)
    and local t n l args ~ctx =
      match Ltree.find t.blks l with
      | None ->
        C.failf
          "Restructure: invalid destination %a in block %a of function $%s"
          Label.pp l Label.pp n (Func.name t.fn) ()
      | Some b ->
        let params = Seq.to_list @@ Blk.args b in
        match List.zip params args with
        | Unequal_lengths ->
          C.failf
            "Restructure: jump from %a to %a in function $%s: \
             arity mismatch (got %d, expected %d)"
            Label.pp n Label.pp l (Func.name t.fn)
            (List.length args) (List.length params) ()
        | Ok moves ->
          (* Emit parallel moves, which removes us from SSA form. *)
          let out = Vec.create () in
          let* () = windmill t n moves out in
          let+ b = branch t ~ctx ~src:n ~dst:l in
          Vec.push out b;
          Stmt.seq @@ Vec.to_list out

    (* Control-flow destination. *)
    and dest t n d ~ctx = match d with
      | #global as g -> !!(`goto g)
      | `label (l, args) -> local t n l args ~ctx

    and br ?k t n c yes no ~ctx =
      let j = possible_join t n ~ctx in
      let ctx' = match j with
        | Some j -> Region.push_join j ctx
        | None -> ctx in
      let* syes = dest t n yes ~ctx:ctx' in
      let+ sno = dest t n no ~ctx:ctx' in
      terminate ?join:j ctx @@ match k with
      | Some k -> `ite (k, syes, sno)
      | None -> `ite (`var c, syes, sno)

    and sw t n ty i d dargs tbl ~ctx =
      let j = possible_join t n ~ctx in
      let ctx' = match j with
        | Some j -> Region.push_switch j ctx
        | None -> ctx in
      let* cs =
        Ctrl.Table.enum tbl |>
        C.Seq.map ~f:(fun (i, `label (l, args)) ->
            let+ c = local t n l args ~ctx:ctx' in
            `case (i, c)) >>| Seq.to_list in
      let+ d = local t n d dargs ~ctx:ctx' in
      terminate ?join:j ctx @@ `sw (i, ty, cs @ [`default d])

    (* Terminator instruction. *)
    and term ?k t n ~ctx =
      match Ltree.find t.blks n with
      | None ->
        C.failf
          "Restructure: cannot emit terminator for non-existent block \
           %a in function $%s" Label.pp n (Func.name t.fn) ()
      | Some b -> match Blk.ctrl b with
        | `ret _ as r -> !!(terminate ctx r)
        | `hlt -> !!(terminate ctx `hlt)
        | `jmp d -> dest t n d ~ctx >>| terminate ctx
        | `br (c, yes, no) -> br ?k t n c yes no ~ctx
        | `sw (ty, i, `label (d, dargs), tbl) ->
          sw t n ty i d dargs tbl ~ctx

    (* Loop region.

       pre: `n` is a loop header
    *)
    and loop t n ~ctx =
      let lp = Option.value_exn @@ Loops.blk t.loop n in
      let j = loop_exit t lp in
      let ctx' = Region.push_loop n lp ctx in
      let ctx' = match j with
        | None -> ctx'
        | Some j -> Region.push_join j ctx' in
      let* body = plain t n ~ctx:ctx' in
      match j with
      | None -> !!(`loop body)
      | Some j ->
        (* XXX: we emit the join point (loop exit) eagerly, but can
           we skip this if it is an active region? *)
        let+ j = node t j ~ctx in
        `seq (`loop body, j)

    (* Plain body and terminator. *)
    and plain t n ~ctx =
      let k = find_single_use_cond t n in
      let kb = Option.map k ~f:fst in
      let kt = Option.map k ~f:snd in
      let* body = body ?k:kb t n in
      let* term = term ?k:kt t n ~ctx in
      match term.join with
      | None -> !!(`seq (body, term.stmt))
      | Some j ->
        let+ sj = node t j ~ctx in
        `seq (body, `seq (term.stmt, sj))

    (* Main entry point. *)
    and node t n ~ctx =
      if Hash_set.mem t.labl n then
        (* Re-entering a node that already has a label, so
           insert a goto. *)
        !!(`goto (`label n))
      else match Hash_set.strict_add t.work n with
        | Error _ ->
          (* We're in the middle of emitting this node, and we
             re-entered it, so ensure that it will be enclosed
             within an explicit label. *)
          Hash_set.add t.labl n;
          !!(`goto (`label n))
        | Ok () ->
          let+ body =
            if Loops.is_header t.loop n
            then loop t n ~ctx
            else plain t n ~ctx in
          Hash_set.remove t.work n;
          if Hash_set.mem t.labl n then `label (n, body) else body
  end

  let run ~tenv fn =
    let t = init ~tenv fn in
    let start = Func.entry fn in
    let+ body = Emit.plain t start ~ctx:empty_ctx in
    let body = Stmt.normalize body in
    Structured_func.create () ~body
      ~dict:(Func.dict fn) ~name:(Func.name fn)
      ~args:(Seq.to_list @@ Func.args fn)
      ~slots:(Vec.to_list t.slot)
end
