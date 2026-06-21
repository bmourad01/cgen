open Core
open Monads.Std
open Virtual
open Remove_dead_vars_impl

module E = Monad.Result.Error
module Vset = Var.Tree_set

(* Even if the result of a div/rem may be unused, if the instruction has
   the potential to trap then removing it will change the semantics. *)
let check_div_rem d = function
  | `bop (_, (`div #Type.imm | `udiv _ | `rem #Type.imm | `urem _), _, r) ->
    begin match r with
      | `int (i, _) -> Bv.(i = zero)
      | _ -> not @@ Dict.mem d Tags.div_rem_nonzero
    end
  | _ -> false

let map_loc unused : local -> local * bool = function
  | `label (l, args) as loc -> match Label.Tree.find unused l with
    | Some s -> `label (l, List.filteri args ~f:(noti s)), true
    | None -> loc, false

let map_dst unused : dst -> dst * bool = function
  | #local as l ->
    let l, changed = map_loc unused l in
    (l :> dst), changed
  | #global as g -> g, false

let map_tbl m unused tbl =
  let changed = ref false in
  let tbl = m tbl ~f:(fun i l ->
      let l, c = map_loc unused l in
      changed := !changed || c;
      i, l) in
  tbl, !changed

let map_ctrl m unused c =
  let loc = map_loc unused in
  let dst = map_dst unused in
  match c with
  | `hlt -> `hlt, false
  | `jmp d ->
    let d, cd = dst d in
    `jmp d, cd
  | `br (c, y, n) ->
    let y, cy = dst y in
    let n, cn = dst n in
    `br (c, y, n), (cy || cn)
  | `ret _ as r -> r, false
  | `sw (t, i, d, tbl) ->
    let d, cd = loc d in
    let tbl, ct = map_tbl m unused tbl in
    `sw (t, i, d, tbl), (cd || ct)

let var_opt : operand -> Var.t option = function
  | `var x -> Some x
  | #const -> None

let local_feed : local -> Label.t * Var.t option list = function
  | `label (l, args) -> l, List.map args ~f:var_opt

let dst_feed : dst -> (Label.t * Var.t option list) list = function
  | `label (l, args) -> [l, List.map args ~f:var_opt]
  | #global -> []

let ctrl_roots = function
  | `hlt | `jmp _ -> Vset.empty
  | `br (x, _, _) -> Vset.singleton x
  | `sw (_, `var v, _, _) -> Vset.singleton v
  | `sw (_, `sym _, _, _) -> Vset.empty

let ctrl_locals enum = function
  | `hlt | `ret _ -> []
  | `jmp d -> dst_feed d
  | `br (_, y, n) -> dst_feed y @ dst_feed n
  | `sw (_, _, d, tbl) ->
    local_feed d ::
    (enum tbl |> Sequence.to_list |> List.map ~f:(fun (_, l) -> local_feed l))

module V = Make(struct
    module Insn = struct
      include Insn
      let check_div_rem i = check_div_rem (Insn.dict i) (Insn.op i)
    end

    module Ctrl = struct
      include Ctrl
      let roots = function
        | `ret None -> Vset.empty
        | `ret (Some a) -> (match var_opt a with
            | Some x -> Vset.singleton x
            | None -> Vset.empty)
        | (`hlt | `jmp _ | `br _ | `sw _) as c -> ctrl_roots c
      let locals = ctrl_locals Ctrl.Table.enum
    end

    module Blk = Blk
    module Func = Func

    let map_ctrl = map_ctrl Ctrl.Table.map_exn
  end)

module A = Make(struct
    open Abi

    module Insn = struct
      include Insn

      let check_div_rem i = check_div_rem (Insn.dict i) (Insn.op i)

      (* Even for instructions like `regcopy` and `stkargs`, they can
         be thought of as pure in the sense that we can discard them
         if they aren't used; the caveat is they cannot be trivially
         rescheduled.

         For calls, it doesn't matter if it returns zero or more results,
         because it is effectful.
      *)
      let lhs i = match Abi.Insn.op i with
        | `bop (x, _, _, _)
        | `uop (x, _, _)
        | `sel (x, _, _, _, _)
        | `load (x, _, _)
        | `regcopy (x, _, _)
        | `stkargs x -> Some x
        | `store _
        | `regstore _
        | `regassign _
        | `call _ -> None
    end

    module Ctrl = struct
      include Ctrl

      let roots : t -> Vset.t = function
        | (`tailcall _ | `ret _) as c -> Ctrl.free_vars c
        | (`hlt | `jmp _ | `br _ | `sw _) as c -> ctrl_roots c

      let locals : t -> (Label.t * Var.t option list) list = function
        | `tailcall _ -> []
        | (`hlt | `jmp _ | `br _ | `ret _ | `sw _) as c ->
          ctrl_locals Ctrl.Table.enum c
    end

    module Blk = Blk
    module Func = Func

    let map_ctrl unused (c : Ctrl.t) : Ctrl.t * bool = match c with
      | `tailcall _ -> c, false
      | (`hlt | `jmp _ | `br _ | `ret _ | `sw _) as c ->
        let c, b = map_ctrl Ctrl.Table.map_exn unused c in
        (c :> Ctrl.t), b
  end)

let run fn =
  if Dict.mem (Func.dict fn) Tags.ssa then
    try Ok (V.run fn) with
    | Invalid_argument msg ->
      E.failf "In Remove_dead_vars: %s" msg ()
  else
    E.failf "In Remove_dead_vars: expected SSA form for function $%s"
      (Func.name fn) ()

let run_abi fn =
  if Dict.mem (Abi.Func.dict fn) Tags.ssa then
    try Ok (A.run fn) with
    | Invalid_argument msg ->
      E.failf "In Remove_dead_vars (ABI): %s" msg ()
  else
    E.failf "In Remove_dead_vars (ABI): expected SSA form for function $%s"
      (Abi.Func.name fn) ()
