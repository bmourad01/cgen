(* This transformation attempts to detect suboptimal/naiive encodings
   of short-circuiting AND/OR logic (see relevant examples in the
   testsuite).

   These sorts of cases are common in front-end generated code
   (e.g. a possible C front-end).
*)

open Core
open Monads.Std
open Regular.Std
open Virtual
open Simplify_cfg_common

module O = Monad.Option

open O.Let
open O.Syntax

let is_empty = Fn.compose Seq.is_empty Blk.insns

let cmp_true b = match Seq.next @@ Blk.insns b with
  | Some (i, is) when Seq.is_empty is ->
    begin match Insn.op i with
      (* Not equal to zero. *)
      | `bop (k, `ne _, `var v, `int (n, _))
      | `bop (k, `ne _, `int (n, _), `var v)
        when Bv.(n = zero) -> Some (k, v, true)
      (* Equal to one. *)
      | `bop (k, `eq _, `var v, `int (n, _))
      | `bop (k, `eq _, `int (n, _), `var v)
        when Bv.(n = one) -> Some (k, v, true)
      | _ -> None
    end
  | _ -> None

let cmp_false b = match Seq.next @@ Blk.insns b with
  | Some (i, is) when Seq.is_empty is ->
    begin match Insn.op i with
      (* Not equal to one. *)
      | `bop (k, `ne _, `var v, `int (n, _))
      | `bop (k, `ne _, `int (n, _), `var v)
        when Bv.(n = one) -> Some (k, v, false)
      (* Equal to zero. *)
      | `bop (k, `eq _, `var v, `int (n, _))
      | `bop (k, `eq _, `int (n, _), `var v)
        when Bv.(n = zero) -> Some (k, v, false)
      | _ -> None
    end
  | _ -> None

(* These cases should be mutually exclusive. *)
let try_cmp b =
  Option.merge (cmp_true b) (cmp_false b)
    ~f:(fun _ _ -> assert false)

let argidx b c =
  Blk.args b |>
  Seq.findi ~f:(fun _ -> Var.equal c) |>
  Option.map ~f:fst

let collect_cond_phi env =
  Hashtbl.fold env.blks ~init:Label.Tree.empty
    ~f:(fun ~key ~data:b acc ->
        if is_empty b then match Blk.ctrl b with
          | `br (c, y, n) ->
            argidx b c |> Option.value_map ~default:acc ~f:(fun i ->
                Label.Tree.set acc ~key ~data:(y, n, i, false))
          | _ -> acc
        else match try_cmp b with
          | None -> acc
          | Some (k, v, truth) -> match Blk.ctrl b with
            | `br (c, y, n) when Var.(c = k) ->
              argidx b v |> Option.value_map ~default:acc ~f:(fun i ->
                  let y, n = if truth then y, n else n, y in
                  Label.Tree.set acc ~key ~data:(y, n, i, true))
            | _ -> acc)

let is_var env x = function
  | `var y ->
    Var.(x = y) ||
    Hashtbl.find env.flag y |>
    Option.value_map ~default:false ~f:(Var.equal x)
  | _ -> false

let brcond env cphi c d ~f =
  Option.value ~default:d @@ match d with
  | `label (l, args) ->
    let* y, n, i, _ = Label.Tree.find cphi l in
    let* arg = List.nth args i in
    let+ () = O.guard @@ is_var env c arg in
    f y n
  | _ -> None

let redir changed env cphi =
  Hashtbl.map_inplace env.blks ~f:(fun b ->
      match Blk.ctrl b with
      | `br (c, y, n) ->
        let y' = brcond env cphi c y ~f:(fun y _ -> changed := true; y) in
        let n' = brcond env cphi c n ~f:(fun _ n -> changed := true; n) in
        if phys_equal y y' && phys_equal n n' then b else
          let () = Logs.debug (fun m ->
              m "%s: block %a: simplified br c=%a, y=%a, n=%a: y'=%a, n'=%a%!"
                __FUNCTION__ Label.pp (Blk.label b)
                Var.pp c pp_dst y pp_dst n
                pp_dst y' pp_dst n') in
          Blk.with_ctrl b @@ `br (c, y', n')
      | `jmp (`label (l, args) as loc) ->
        Option.value ~default:b begin
          let* y, n, i, ne = Label.Tree.find cphi l in
          let* x = List.nth args i >>= var_of_operand in
          let+ c = if ne then Hashtbl.find env.flag x else !!x in
          changed := true;
          Logs.debug (fun m ->
              m "%s: block %a: simplified jmp %a: c=%a, y=%a, n=%a%!"
                __FUNCTION__ Label.pp (Blk.label b)
                pp_local loc Var.pp c pp_dst y pp_dst n);
          Blk.with_ctrl b @@ `br (c, y, n)
        end
      | _ -> b)

let run env =
  let changed = ref false in
  let cphi = collect_cond_phi env in
  if not @@ Label.Tree.is_empty cphi then
    redir changed env cphi;
  !changed
