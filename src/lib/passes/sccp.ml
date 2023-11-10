open Core
open Graphlib.Std
open Regular.Std
open Virtual

module I = Bv_interval

type cursor =
  | Blk of Label.t
  | Insn of Label.t

type env = {
  mutable cur : cursor;
  tenv        : Typecheck.env;
  intv        : Intervals.t;
  fn          : func;
}

let init tenv intv fn = {
  cur = Blk Label.pseudoentry;
  tenv;
  intv;
  fn;
}

let typeof_var env x =
  match Typecheck.Env.typeof_var env.fn x env.tenv with
  | Error err -> failwithf "%s" (Error.to_string_hum err) ()
  | Ok ty -> ty

let var env x =
  let s = match env.cur with
    | Blk l -> Solution.get (Intervals.input env.intv) l
    | Insn l ->
      Intervals.insn env.intv l |>
      Option.value ~default:Intervals.empty_state in
  Intervals.find_var s x

let word env = Target.word @@ Typecheck.Env.target env.tenv

let map_operand env : operand -> operand = function
  | `var x as o ->
    begin match var env x with
      | None -> o
      | Some i -> match I.single_of i with
        | None -> o
        | Some v -> match typeof_var env x with
          | #Type.imm as imm -> `int (v, imm)
          | _ -> o
    end
  | o -> o

let map_local env : local -> local = function
  | `label (l, args) ->
    `label (l, List.map args ~f:(map_operand env))

let map_global env : global -> global = function
  | `addr _ | `sym _ as g -> g
  | `var x as g -> match var env x with
    | None -> g
    | Some i -> match I.single_of i with
      | None -> g
      | Some v -> match typeof_var env x with
        | #Type.imm_base as t ->
          if Type.equal_imm_base t @@ word env
          then `addr v else g
        | _ -> g

let map_dst env : dst -> dst = function
  | #global as g -> (map_global env g :> dst)
  | #local as l -> (map_local env l :> dst)

let map_sel env x t c l r =
  let l = map_operand env l in
  let r = map_operand env r in
  match var env x with
  | Some i when I.(equal i boolean_true) ->
    `uop (x, `copy t, l)
  | Some i when I.(equal i boolean_false) ->
    `uop (x, `copy t, r)
  | Some _ | None -> `sel (x, t, c, l, r)

let map_alist env : Insn.alist -> Insn.alist = function
  | `addr _ | `sym _ as a -> a
  | `var x as a -> match var env x with
    | None -> a
    | Some i -> match I.single_of i with
      | None -> a
      | Some v -> match typeof_var env x with
        | #Type.imm_base as t ->
          if Type.equal_imm_base t @@ word env
          then `addr v else a
        | _ -> a

let cannot_be_zero env x = match var env x with
  | Some i -> not @@ I.contains_value i Bv.zero
  | None -> false

let map_op env (op : Insn.op) = 
  let operand = map_operand env in
  match op with
  | `bop (x, (`div (#Type.imm as t) | `udiv t), `var y, `var z)
    when Var.(y = z) && cannot_be_zero env z ->
    `uop (x, `copy (t :> Type.basic), `int (Bv.one, t))
  | `bop (x, (`rem (#Type.imm as t) | `urem t), `var y, `var z)
    when Var.(y = z) && cannot_be_zero env z ->
    `uop (x, `copy (t :> Type.basic), `int (Bv.zero, t))
  | `bop (x, b, l, r) ->
    `bop (x, b, operand l, operand r)
  | `uop (x, u, a) -> `uop (x, u, operand a)
  | `sel (x, t, c, l, r) -> map_sel env x t c l r
  | `call (x, f, args, vargs) ->
    let f = map_global env f in
    let args = List.map args ~f:operand in 
    let vargs = List.map vargs ~f:operand in
    `call (x, f, args, vargs)
  | `load (x, t, a) -> `load (x, t, operand a)
  | `store (t, v, a) -> `store (t, operand v, operand a)
  | `vastart a -> `vastart (map_alist env a)
  | `vaarg (x, t, a) -> `vaarg (x, t, map_alist env a)

(* Based on the intervals analysis, we can safely remove a div/rem
   whose RHS is known to never be zero. *)
let mark_div_rem_nonzero env i = match Insn.op i with
  | `bop (_, b, _, `var x) ->
    begin match b with
      | `div #Type.imm
      | `udiv _
      | `rem #Type.imm
      | `urem _ ->
        let l = Insn.label i in
        begin match Intervals.insn env.intv l with
          | None -> i
          | Some s -> match Intervals.find_var s x with
            | None -> i
            | Some iv when Bv_interval.contains_value iv Bv.zero -> i
            | Some _ -> Insn.with_tag i Tags.div_rem_nonzero ()
        end
      | _ -> i
    end
  | _ -> i

let map_insn env i =
  mark_div_rem_nonzero env @@
  Insn.with_op i @@
  map_op env @@
  Insn.op i

let map_tbl_entry env i l = i, map_local env l

let map_br env c y n =
  let y = map_dst env y in
  let n = map_dst env n in
  match var env c with
  | Some i when I.(equal i boolean_true) -> `jmp y
  | Some i when I.(equal i boolean_false) -> `jmp n
  | Some _ | None -> `br (c, y, n)

let map_sw env t i d tbl =
  let d = map_local env d in
  let tbl = Ctrl.Table.map_exn tbl ~f:(map_tbl_entry env) in
  match i with
  | `sym _ -> `sw (t, i, d, tbl)
  | `var x -> match var env x with
    | None -> `sw (t, i, d, tbl)
    | Some iv -> match I.single_of iv with
      | None -> `sw (t, i, d, tbl)
      | Some v ->
        let d = Ctrl.Table.find tbl v |> Option.value ~default:d in
        `jmp (d :> dst)

let map_ctrl env : ctrl -> ctrl = function
  | `hlt -> `hlt
  | `jmp d -> `jmp (map_dst env d)
  | `br (c, y, n) -> map_br env c y n
  | `ret None as c -> c
  | `ret Some x -> `ret (Some (map_operand env x))
  | `sw (t, i, d, tbl) -> map_sw env t i d tbl
  | `tcall (t, f, args, vargs) ->
    let f = map_global env f in
    let args = List.map args ~f:(map_operand env) in 
    let vargs = List.map vargs ~f:(map_operand env) in
    `tcall (t, f, args, vargs)

let map_blk env b =
  let insns =
    Blk.insns b |> Seq.to_list |> List.map ~f:(fun i ->
        env.cur <- Insn (Insn.label i);
        map_insn env i) in
  if List.is_empty insns then env.cur <- Blk (Blk.label b);
  let ctrl = map_ctrl env @@ Blk.ctrl b in
  let args = Blk.args b |> Seq.to_list in
  let dict = Blk.dict b in
  let label = Blk.label b in
  Blk.create ~dict ~args ~insns ~ctrl ~label ()

let try_ f = try Ok (f ()) with
  | Invalid_argument msg
  | Failure msg -> Or_error.errorf "%s" msg

let run tenv fn = try_ @@ fun () ->
  let word = Target.word @@ Typecheck.Env.target tenv in
  let typeof x = match Typecheck.Env.typeof_var fn x tenv with
    | Error err -> failwith @@ Error.to_string_hum err
    | Ok t -> t in
  let intv = Intervals.analyze fn ~word ~typeof in
  let env = init tenv intv fn in
  Func.map_blks fn ~f:(map_blk env)
