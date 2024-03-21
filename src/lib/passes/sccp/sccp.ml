open Core
open Regular.Std
open Virtual

module I = Bv_interval
module Intervals = Sccp_intervals

type cursor = Blk | Insn

type env = {
  mutable cur : cursor;
  mutable pos : Label.t;
  tenv        : Typecheck.env;
  intv        : Intervals.t;
  fn          : func;
}

let init tenv intv fn = {
  cur = Blk;
  pos = Label.pseudoentry;
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
    | Blk -> Intervals.input env.intv env.pos
    | Insn -> Intervals.insn env.intv env.pos in
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
  match var env c with
  | Some i when I.(equal i boolean_true) ->
    `uop (x, `copy t, l)
  | Some i when I.(equal i boolean_false) ->
    `uop (x, `copy t, r)
  | Some _ | None -> `sel (x, t, c, l, r)

let map_op env (op : Insn.op) = 
  let operand = map_operand env in
  match op with
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
  | `vastart a -> `vastart (map_global env a)
  | `vaarg (x, t, a) -> `vaarg (x, t, map_global env a)

(* Based on the intervals analysis, we can safely remove a div/rem
   whose RHS is known to never be zero. *)
let mark_div_rem_nonzero env i = match Insn.op i with
  | `bop (_, b, _, `var x) ->
    begin match b with
      | `div #Type.imm
      | `udiv _
      | `rem #Type.imm
      | `urem _ ->
        let s = Intervals.insn env.intv @@ Insn.label i in
        begin match Intervals.find_var s x with
          | Some iv when Bv_interval.contains_value iv Bv.zero -> i
          | Some _ -> Insn.with_tag i Tags.div_rem_nonzero ()
          | None -> i
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
  let default_tbl = lazy (Ctrl.Table.map_exn tbl ~f:(map_tbl_entry env)) in
  match i with
  | `sym _ -> `sw (t, i, d, Lazy.force default_tbl)
  | `var x -> match var env x with
    | None -> `sw (t, i, d, Lazy.force default_tbl)
    | Some iv ->
      (* Filter out cases of the switch that will never be true. *)
      Ctrl.Table.enum tbl |>
      Seq.filter_map ~f:(fun (i, l) ->
          if I.contains_value iv i
          then Some (i, map_local env l)
          else None) |> Seq.to_list |> function
      | [] -> `jmp (d :> dst)
      | lst -> match I.single_of iv with
        | None -> `sw (t, i, d, Ctrl.Table.create_exn lst t)
        | Some v ->
          (* The index is a known constant, so collapse the
             switch into a jump. *)
          let d =
            Option.value ~default:d @@
            List.find_map lst ~f:(fun (u, l) ->
                Option.some_if Bv.(u = v) l) in
          `jmp (d :> dst)

let map_ctrl env : ctrl -> ctrl = function
  | `hlt -> `hlt
  | `jmp d -> `jmp (map_dst env d)
  | `br (c, y, n) -> map_br env c y n
  | `ret None as c -> c
  | `ret Some x -> `ret (Some (map_operand env x))
  | `sw (t, i, d, tbl) -> map_sw env t i d tbl

let map_blk env b =
  let insns = Blk.insns b |> Seq.map ~f:(fun i ->
      env.cur <- Insn;
      env.pos <- Insn.label i;
      map_insn env i) |> Seq.to_list in
  if List.is_empty insns then begin
    env.cur <- Blk;
    env.pos <- Blk.label b
  end;
  let ctrl = map_ctrl env @@ Blk.ctrl b in
  let args = Blk.args b |> Seq.to_list in
  let dict = Blk.dict b in
  let label = Blk.label b in
  Blk.create ~dict ~args ~insns ~ctrl ~label ()

let try_ f = try Ok (f ()) with
  | Invalid_argument msg
  | Failure msg -> Or_error.errorf "In SCCP: %s" msg

let run tenv fn = try_ @@ fun () ->
  let word = Target.word @@ Typecheck.Env.target tenv in
  let typeof x = match Typecheck.Env.typeof_var fn x tenv with
    | Error err -> failwith @@ Error.to_string_hum err
    | Ok t -> t in
  let intv = Intervals.analyze fn ~word ~typeof in
  let env = init tenv intv fn in
  Func.map_blks fn ~f:(map_blk env)
