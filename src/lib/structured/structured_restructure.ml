open Core
open Regular.Std
open Graphlib.Std
open Virtual

module Ltree = Label.Tree
module Stmt = Structured_stmt

type blks = blk Ltree.t

type t = {
  fn    : func;
  tenv  : Typecheck.env;
  blks  : blks;
  cfg   : Cfg.t;
  pdom  : Label.t Semi_nca.tree;
  pdomd : Label.t -> int;
  loop  : Loops.t;
  live  : Live.t;
}

let init_domd tree start =
  let t = Label.Table.create () in
  let q = Stack.singleton (start, 0) in
  Stack.until_empty q (fun (l, d) ->
      Hashtbl.set t ~key:l ~data:d;
      Semi_nca.Tree.children tree l |>
      Seq.iter ~f:(fun c -> Stack.push q (c, d + 1)));
  Hashtbl.find_exn t

let init ~tenv fn =
  let cfg = Cfg.create fn in
  let blks = Func.map_of_blks fn in
  let dom = Semi_nca.compute (module Cfg) cfg Label.pseudoentry in
  let loop = Loops.analyze ~dom ~name:(Func.name fn) cfg in
  let pdom = Semi_nca.compute (module Cfg) ~rev:true cfg Label.pseudoexit in
  let pdomd = init_domd pdom Label.pseudoexit in
  let live = Live.compute' cfg blks in
  {fn; tenv; blks; cfg; pdom; pdomd; loop; live}

(* Lowest common ancestor of a tree. *)
let lca ~idom ~depth a b =
  let ra = ref a
  and rb = ref b
  and da = ref (depth a)
  and db = ref (depth b) in
  (* While `a` is deeper than `b`, go up the tree. *)
  while !da > !db do
    ra := idom !ra;
    decr da;
  done;
  (* While `b` is deeper than `a`, go up the tree. *)
  while !db > !da do
    rb := idom !rb;
    decr db;
  done;
  (* Find the common ancestor. *)
  while Label.(!ra <> !rb) do
    ra := idom !ra;
    rb := idom !rb;
  done;
  !ra

(* Lowest common ancestor of the post-dominator tree. *)
let lca_pdom t a b =
  let idom l = match Semi_nca.Tree.parent t.pdom l with
    | None -> assert false
    | Some p -> p in
  lca a b ~idom ~depth:t.pdomd

let lca_pdom_list t = function
  | [] -> None
  | [s] -> Some s
  | s :: rest ->
    Some (List.fold rest ~init:s ~f:(lca_pdom t))

let loop_exit t lp =
  let rec climb j =
    if Loops.is_in_loop t.loop j lp then
      match Semi_nca.Tree.parent t.pdom j with
      | Some p -> climb p
      | None -> None
    else if Ltree.mem t.blks j then Some j
    else None in
  climb Loops.(header @@ get t.loop lp)

let parent_loop_header t lp =
  Loops.get t.loop lp |> Loops.parent |>
  Option.map ~f:(fun p -> Loops.(header @@ get t.loop p))

let possible_join t n =
  Cfg.Node.succs n t.cfg |> Seq.to_list |>
  lca_pdom_list t |> Option.bind ~f:(fun j ->
      Option.some_if begin
        (* The block exists (i.e. not a pseudo label) *)
        Ltree.mem t.blks j &&
        (* If this join point is in any stack of loops,
           then `n` (our source node) is within all of
           them. *)
        Loops.loops_of t.loop j |>
        Seq.for_all ~f:(Loops.is_in_loop t.loop n)
      end j)

(* A current "region" that we're exploring.

   [Loop h]: a loop with header label [h]
   [Join j]: a region with join point label [j]
   [Switch s]: a switch region with a join point label [s]
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

(* The current stack of regions. *)
type ctx = {
  frames : frame list;
} [@@unboxed]

module Region = struct
  let empty = {frames = []}

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

  let outside_current_loop t j ~ctx =
    match ctx.frames with
    | Loop (_, lp) :: _ ->
      not (Loops.is_in_loop t.loop j lp)
    | Join _ :: Loop (_, lp) :: _ ->
      not (Loops.is_in_loop t.loop j lp)
    | Switch _ :: Loop (_, lp) :: _ ->
      not (Loops.is_in_loop t.loop j lp)
    | _ -> false
end

(* Shared state for the whole transformation.

   [in_progress]: the nodes that we're currently emitting
   [scheduled]: the nodes that have been made the target of a goto
*)
type state = {
  in_progress : Label.Hash_set.t;
  scheduled   : Label.Hash_set.t;
}

let create_state () = {
  in_progress = Label.Hash_set.create ();
  scheduled = Label.Hash_set.create ();
}

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

module Classify : sig
  val jmp : t -> ctx:ctx -> src:Label.t -> dst:Label.t -> jmpcls
end = struct
  let continue t ~ctx ~dst =
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
  let break_switch t ~ctx ~dst = match ctx.frames with
    | Switch s :: _ -> Label.(s = dst)
    | _ -> false

  (* Jumps to nearest join point. *)
  let fallthrough t ~ctx ~dst = match ctx.frames with
    | Join j :: _ -> Label.(j = dst)
    | _ -> false

  (* Emitting a `continue` is safe, but if a fallthrough
     is semantically valid here then we should prefer that,
     as it is a bit cleaner. *)
  let continue_or_fallthrough t ~ctx ~dst =
    let lp = Option.value_exn @@ Loops.blk t.loop dst in
    match loop_exit t lp with
    | Some j when fallthrough t ~ctx ~dst:j -> Fallthrough
    | Some _ | None -> Continue

  let debug_jmp t ctx src dst =
    Logs.debug (fun m ->
        m "%s: $%s: src=%a, dst=%a, stack:@;@[<v 0>%a@]%!"
          __FUNCTION__ (Func.name t.fn) Label.pp src Label.pp dst
          (Format.pp_print_list
             ~pp_sep:(fun ppf () -> Format.fprintf ppf "@;")
             pp_frame) ctx.frames)

  let jmp t ~ctx ~src ~dst =
    debug_jmp t ctx src dst;
    if continue t ~ctx ~dst then continue_or_fallthrough t ~ctx ~dst
    else if break_switch t ~ctx ~dst then Break
    else if break_loop t ~ctx ~dst then Break
    else if fallthrough t ~ctx ~dst then Fallthrough
    else Inline
end

let op i = (Insn.op i :> Stmt.t)

(* See if this block has a single-use comparison that we
   can fold into the `ite` statement. *)
let find_cond t n =
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
              let label = Insn.label i
              and k = `cmp (cmp, l, r) in
              Some (label, k)
            | _ -> None)
      | _ -> None)

module Make(C : Context_intf.S) = struct
  open C.Syntax

  let typeof_var t x =
    Typecheck.Env.typeof_var t.fn x t.tenv |>
    C.lift_err ~prefix:"Restructure"

  module W = Windmill.Make(C)

  let windmill out t l moves =
    W.windmill t l moves ~emit:(fun dst src ->
        typeof_var t dst >>= function
        | #Type.basic as b ->
          C.return @@ Vec.push out @@ `uop (dst, `copy b, src)
        | _t ->
          (* TODO: fix this *)
          assert false)

  module Emit = struct
    (* Plain sequence of instructions. *)
    let body ?k t n = match Ltree.find t.blks n with
      | Some b ->
        let s = match k with
          | None -> Blk.insns b
          | Some k ->
            Blk.insns b |> Seq.filter ~f:(fun i ->
                not @@ Label.equal k @@ Insn.label i) in
        Seq.map s ~f:op |> Seq.to_list |> Stmt.seq |> C.return
      | None ->
        C.failf
          "Restructure: cannot emit body for non-existent \
           block %a in function $%s" Label.pp n (Func.name t.fn) ()

    (* Branch to a block. *)
    let rec branch t ~ctx ~st ~src ~dst =
      let cls = Classify.jmp t ~ctx ~src ~dst in
      Logs.debug (fun m ->
          m "%s: $%s: src=%a, dst=%a, cls=%a%!"
            __FUNCTION__ (Func.name t.fn) Label.pp src
            Label.pp dst pp_jmpcls cls);
      match cls with
      | Fallthrough -> !!`nop
      | Continue -> !!`continue
      | Break -> !!`break
      | Inline -> node t dst ~ctx ~st

    (* Local control-flow destination. *)
    and local t n l args ~ctx ~st =
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
          let* () = windmill out t n moves in
          let+ b = branch t ~ctx ~st ~src:n ~dst:l in
          Vec.push out b;
          Stmt.seq @@ Vec.to_list out

    (* Control-flow destination. *)
    and dest t n d ~ctx ~st = match d with
      | #global as g -> !!(`goto g)
      | `label (l, args) -> local t n l args ~ctx ~st

    and br ?k t n c yes no ~ctx ~st =
      let j = possible_join t n in
      let ctx' = match j with
        | None -> ctx
        | Some j -> Region.push_join j ctx in
      let* yes = dest t n yes ~ctx:ctx' ~st in
      let* no = dest t n no ~ctx:ctx' ~st in
      let ite = match k with
        | None -> `ite (`var c, yes, no)
        | Some k -> `ite (k, yes, no) in
      match j with
      | None -> !!ite
      | Some j when Region.outside_current_loop t j ~ctx -> !!ite
      | Some j ->
        let+ j = node t j ~ctx ~st in
        `seq (ite, j)

    and sw t n ty i d dargs tbl ~ctx ~st =
      let j = possible_join t n in
      let ctx' = match j with
        | Some j -> Region.push_switch j ctx
        | None -> ctx in
      let* cs =
        Ctrl.Table.enum tbl |>
        C.Seq.map ~f:(fun (i, `label (l, args)) ->
            let+ c = local t n l args ~ctx:ctx' ~st in
            `case (i, c)) >>| Seq.to_list in
      let* d = local t n d dargs ~ctx:ctx' ~st in
      let sw = `sw (i, ty, cs @ [`default d]) in
      match j with
      | None -> !!sw
      | Some j when Region.outside_current_loop t j ~ctx -> !!sw
      | Some j ->
        let+ j = node t j ~ctx ~st in
        `seq (sw, j)

    (* Terminator instruction. *)
    and term ?k t n ~ctx ~st =
      match Ltree.find t.blks n with
      | None ->
        C.failf
          "Restructure: cannot emit terminator for non-existent block \
           %a in function $%s" Label.pp n (Func.name t.fn) ()
      | Some b -> match Blk.ctrl b with
        | `ret _ as r -> !!r
        | `hlt -> !!`hlt
        | `jmp d -> dest t n d ~ctx ~st
        | `br (c, yes, no) -> br ?k t n c yes no ~ctx ~st
        | `sw (ty, i, `label (d, dargs), tbl) ->
          sw t n ty i d dargs tbl ~ctx ~st

    (* Loop region. *)
    and loop t n ~ctx ~st =
      let lp = Option.value_exn @@ Loops.blk t.loop n in
      let ctx' = Region.push_loop n lp ctx in
      let* body = plain t n ~ctx:ctx' ~st in
      match loop_exit t lp with
      | None -> !!(`loop body)
      | Some j ->
        let+ j = node t j ~ctx ~st in
        `seq (`loop body, j)

    (* Plain body and terminator. *)
    and plain t n ~ctx ~st =
      let k = find_cond t n in
      let kb = Option.map k ~f:fst in
      let kt = Option.map k ~f:snd in
      let* body = body ?k:kb t n in
      let+ term = term ?k:kt t n ~ctx ~st in
      `seq (body, term)

    (* Main entry point. *)
    and node t n ~ctx ~st =
      if Hash_set.mem st.scheduled n then
        !!(`goto (`label n))
      else match Hash_set.strict_add st.in_progress n with
        | Error _ ->
          Hash_set.add st.scheduled n;
          !!(`goto (`label n))
        | Ok () ->
          let+ body =
            if Loops.is_header t.loop n
            then loop t n ~ctx ~st
            else plain t n ~ctx ~st in
          Hash_set.remove st.in_progress n;
          if Hash_set.mem st.scheduled n
          then `label (n, body) else body
  end

  let run ~tenv fn =
    let t = init ~tenv fn in
    let st = create_state () in
    let ctx = Region.empty in
    let+ body = Emit.plain t (Func.entry fn) ~ctx ~st in
    let body = Stmt.normalize body in
    Structured_func.create () ~body
      ~dict:(Func.dict fn)
      ~name:(Func.name fn)
      ~args:(Seq.to_list @@ Func.args fn)
      ~slots:(Seq.to_list @@ Func.slots fn)
end
