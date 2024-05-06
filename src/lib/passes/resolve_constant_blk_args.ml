open Core
open Regular.Std
open Graphlib.Std
open Virtual

exception Missing of Label.t
exception Redef of Var.t * Label.t
exception Arity of Label.t * Label.t * int * int

let collect_copies blks fn dom =
  let t = Var.Table.create () in
  let q = Stack.singleton @@ Func.entry fn in
  Stack.until_empty q (fun l ->
      Label.Tree.find blks l |> Option.iter ~f:(fun b ->
          Blk.insns b |> Seq.iter ~f:(fun i -> match Insn.op i with
              | `uop (x, `copy _, y) ->
                let data = match y with
                  | `var z -> Hashtbl.find_or_add t z ~default:(const y)
                  | _ -> y in
                (* Should never fail. *)
                begin match Hashtbl.add t ~key:x ~data with
                  | `Duplicate -> raise_notrace @@ Redef (x, Blk.label b)
                  | `Ok -> ()
                end
              | _ -> ()));
      Tree.children dom l |> Seq.iter ~f:(Stack.push q));
  t

(* A variable can have one or many values. *)
type value =
  | One of operand
  | Many
[@@deriving equal]

type state = value Var.Map.t [@@deriving equal]

let join_value cpy x y = match x, y with
  | Many, _ | _, Many -> Many
  | One `var a, One `var b when Var.(a = b) -> x
  | One `var a, One `var b ->
    begin match Hashtbl.(find cpy a, find cpy b) with
      | Some v1, Some v2 when equal_operand v1 v2 -> One v1
      | _ -> Many
    end
  | One `var a, One b ->
    begin match Hashtbl.find cpy a with
      | Some v when equal_operand b v -> y
      | _ -> Many
    end
  | One a, One `var b ->
    begin match Hashtbl.find cpy b with
      | Some v when equal_operand a v -> x
      | _ -> Many
    end
  | One a, One b when equal_operand a b -> x
  | One _, One _ -> Many

let local cpy blks s bl : local -> state = function
  | `label (l, vs) -> match Label.Tree.find blks l with
    | None -> raise_notrace @@ Missing l
    | Some b ->
      let args = Seq.to_list @@ Blk.args b in
      match List.zip args vs with
      | Unequal_lengths ->
        raise_notrace @@ Arity (bl, l, List.length vs, List.length args)
      | Ok xs -> List.fold xs ~init:s ~f:(fun s (x, v) ->
          Map.update s x ~f:(function
              | Some v' -> join_value cpy v' @@ One v
              | None -> One v))

let dst cpy blks s bl : dst -> state = function
  | #local as l -> local cpy blks s bl l
  | #global -> s

let transfer cpy blks l s = match Label.Tree.find blks l with
  | None when Label.is_pseudo l -> s
  | None -> raise_notrace @@ Missing l
  | Some b -> match Blk.ctrl b with
    | `hlt | `ret _ -> s
    | `jmp d -> dst cpy blks s l d
    | `br (_, y, n) ->
      dst cpy blks (dst cpy blks s l y) l n
    | `sw (_, _, d, tbl) ->
      let init = local cpy blks s l d in
      Ctrl.Table.enum tbl |> Seq.fold ~init
        ~f:(fun s (_, l') -> local cpy blks s l l')

let merge cpy = Map.merge_skewed ~combine:(fun ~key:_ -> join_value cpy)

let filter_many = Map.filter_map ~f:(function
    | Many -> None | One v -> Some v)

let analyze fn =
  let cfg = Cfg.create fn in
  let dom = Graphlib.dominators (module Cfg) cfg Label.pseudoentry in
  let blks = Func.map_of_blks fn in
  let cpy = collect_copies blks fn dom in
  let init = Solution.create Label.Map.empty Var.Map.empty in
  let soln = Graphlib.fixpoint (module Cfg) cfg ~init
      ~equal:equal_state ~merge:(merge cpy) ~f:(transfer cpy blks) in
  (* The pseudoexit label should have all of the accumulated results,
     since this is a forward-flow analysis. *)
  filter_many @@ Solution.get soln Label.pseudoexit

let error_prefix = "In Resolve_constant_blk_args"

let try_ fn f = try Ok (f ()) with
  | Missing l ->
    Or_error.errorf "%s: in function $%s, missing block %a"
      error_prefix (Func.name fn) Label.pps l
  | Redef (x, l) ->
    Or_error.errorf "%s: in function $%s, redefinition of variable %a in block %a"
      error_prefix (Func.name fn) Var.pps x Label.pps l
  | Arity (l, l', n, n') ->
    Or_error.errorf "%s: in function $%s, arity mismatch in edge %a -> %a (%d != %d)"
      error_prefix (Func.name fn) Label.pps l Label.pps l' n n'

let run fn =
  if Dict.mem (Func.dict fn) Tags.ssa then try_ fn @@ fun () ->
    let s = analyze fn in
    if not @@ Map.is_empty s then Func.map_blks fn ~f:(fun b ->
        let is, k = Subst_mapper.map_blk s b in
        Blk.(with_ctrl (with_insns b is) k))
    else fn
  else
    Or_error.errorf "%s: function $%s is not in SSA form"
      error_prefix (Func.name fn)
