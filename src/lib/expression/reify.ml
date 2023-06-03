open Core
open Virtual
open Common

type elt = [
  | `insn of Insn.op
  | `ctrl of ctrl
]

let pp_elt ppf : elt -> unit = function
  | `insn o -> Format.fprintf ppf "%a" Insn.pp_op o
  | `ctrl c -> Format.fprintf ppf "%a" Ctrl.pp c

type env = {
  func : elt Label.Tree.t;
  vars : operand Var.Map.t;
}

let empty = {
  func = Label.Tree.empty;
  vars = Var.Map.empty;
}

module M = Sm.Make(struct
    type state = env
    let fail msg = Error.createf "Reify error: %s" msg
  end)

type 'a t = 'a M.m

include M.Syntax

(* Assume that if the key is already present then calling `f`
   will just give the same result. *)
let add l f =
  let* env = M.get () in
  if not @@ Label.Tree.mem env.func l then
    let* x = f () in
    M.put {env with func = Label.Tree.set env.func ~key:l ~data:x}
  else !!()

let set x o =
  let* env = M.get () in
  M.put {
    env with vars = Map.update env.vars x ~f:(function
      | Some x -> x
      | None -> o)
  }

let get l env = match Label.Tree.find env.func l with
  | None -> E.failf "Missing instruction %a" Label.pp l ()
  | Some e -> Ok e

let enum env = Label.Tree.to_sequence env.func

let invalid_insn o l msg = M.fail @@ Error.createf
    "Invalid argument %s for %s instruction %a"
    (Format.asprintf "%a" pp_operand o) msg Label.pps l

let find_var ctx = function
  | Some l ->
    let*? x = find_var ctx l in
    !!(x, l)
  | None ->
    M.fail @@ Error.of_string "Tried to reify an expression with no label"

let rec pure ctx p : operand t =
  let var = find_var ctx in
  let pure = pure ctx in
  let insn l f =
    let* x, l = var l in
    let+ () = add l @@ fun () ->
      let+ o = f x l in
      `insn o in
    `var x in
  match p with
  | Palloc (l, n) -> insn l @@ fun x _ -> !!(`alloc (x, n))
  | Pbinop (l, o, a, b) -> insn l @@ fun x _ ->
    let+ a = pure a and+ b = pure b in
    `bop (x, o, a, b)
  | Pbool f -> !!(`bool f)
  | Pcall (l, t, f, args, vargs) -> insn l @@ fun x _ ->
    let+ f = global ctx f
    and+ args = M.List.map args ~f:pure
    and+ vargs = M.List.map vargs ~f:pure in
    `call (Some (x, t), f, args, vargs)
  | Pdouble d -> !!(`double d)
  | Pint (i, t) -> !!(`int (i, t))
  | Pload (l, t, a) -> insn l @@ fun x _ ->
    let+ a = pure a in
    `load (x, t, a)
  | Psel (l, t, c, y, n) -> insn l @@ fun x l ->
    let* y = pure y and* n = pure n in
    let+ o = pure c >>= function
      | `bool f ->
        let o = if f then y else n in
        (* The op we're returning is a dummy value; we will
           instead substitute uses of `x` with `o`, and later
           this assignment to `x` can be removed as dead code. *)
        let+ () = set x o in
        `uop (x, `copy t, o)
      | `var c -> !!(`sel (x, t, c, y, n))
      | c ->
        invalid_insn c l @@
        Format.asprintf "condition of `sel.%a`"
          Type.pp (t :> Type.t) in
    o
  | Psingle s -> !!(`float s)
  | Psym (s, n) -> !!(`sym (s, n))
  | Punop (l, o, a) -> insn l @@ fun x _ ->
    let+ a = pure a in
    `uop (x, o, a)
  | Pvar x -> M.gets @@ fun {vars; _} ->
    Map.find vars x |> Option.value ~default:(`var x)

and global ctx : global -> Virtual.global t = function
  | Gaddr a -> !!(`addr a)
  | Gpure p ->
    let* p = pure ctx p in
    let+ g = match p with
      | `var x -> !!(`var x)
      | `int (i, _) -> !!(`addr i)
      | op ->
        M.fail @@
        Error.createf "Invalid global %s" @@
        Format.asprintf "%a" pp_operand op in
    g
  | Gsym s -> !!(`sym s)

let local ctx : local -> Virtual.local t = function
  | l, args ->
    let+ args = M.List.map args ~f:(pure ctx) in
    `label (l, args)

let dst ctx : dst -> Virtual.dst t = function
  | Dglobal g ->
    let+ g = global ctx g in
    (g :> Virtual.dst)
  | Dlocal l ->
    let+ l = local ctx l in
    (l :> Virtual.dst)

let table ctx tbl t =
  M.List.map tbl ~f:(fun (i, l) ->
      let+ l = local ctx l in
      i, l) >>| fun tbl ->
  Ctrl.Table.create_exn tbl t

let table_dst tbl i d =
  Ctrl.Table.find tbl i |>
  Option.value ~default:d |> fun l ->
  (l :> Virtual.dst)

let exp ctx l e =
  let pure = pure ctx in
  let dst = dst ctx in
  let insn f = add l @@ fun () -> let+ o = f () in `insn o in
  let ctrl f = add l @@ fun () -> let+ c = f () in `ctrl c in
  match e with
  | Ebr (c, y, n) -> ctrl @@ fun () ->
    let* y = dst y and* n = dst n in
    let+ op = pure c >>= function
      | `bool f -> !!(`jmp (if f then y else n))
      | `var _ when Virtual.equal_dst y n -> !!(`jmp y)
      | `var c -> !!(`br (c, y, n))
      | c -> invalid_insn c l "condition of `br`" in
    op
  | Ecall (f, args, vargs) -> insn @@ fun () ->
    let+ f = global ctx f
    and+ args = M.List.map args ~f:pure
    and+ vargs = M.List.map vargs ~f:pure in
    `call (None, f, args, vargs)
  | Ehlt -> ctrl @@ fun () -> !!`hlt
  | Ejmp d -> ctrl @@ fun () ->
    let+ d = dst d in
    `jmp d
  | Eret None -> ctrl @@ fun () -> !!(`ret None)
  | Eret (Some r) -> ctrl @@ fun () ->
    let+ r = pure r in
    `ret (Some r)
  | Eset (_, y) -> pure y >>| ignore
  | Estore (t, v, a) -> insn @@ fun () ->
    let+ v = pure v and+ a = pure a in
    `store (t, v, a)
  | Esw (t, i, d, tbl) -> ctrl @@ fun () ->
    let* d = local ctx d
    and* tbl = table ctx tbl t in
    let+ op = pure i >>= function
      | (`var _ | `sym _) as i -> !!(`sw (t, i, d, tbl))
      | `int (i, _) -> !!(`jmp (table_dst tbl i d))
      | i -> invalid_insn i l "index of `sw`" in
    op
  | Evaarg (x, t, a) -> insn @@ fun () -> !!(`vaarg (x, t, a))
  | Evastart x -> insn @@ fun () -> !!(`vastart x)

let run ?(init = empty) ctx l e = (exp ctx l e).run init
    ~reject:(fun e -> Error e)
    ~accept:(fun () env -> Ok env)
