open Core
open Regular.Std
open Graphlib.Std
open Virtual

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
                Hashtbl.add_exn t ~key:x ~data
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

let local cpy blks s : local -> state = function
  | `label (_, []) -> s
  | `label (l, vs) ->
    Label.Tree.find blks l |>
    Option.value_map ~default:s ~f:(fun b ->
        let args = Seq.to_list @@ Blk.args b in
        List.zip_exn args vs |>
        List.fold ~init:s ~f:(fun s (x, v) ->
            Map.update s x ~f:(function
                | Some v' -> join_value cpy v' @@ One v
                | None -> One v)))

let dst cpy blks s : dst -> state = function
  | #local as l -> local cpy blks s l
  | #global -> s

let transfer cpy blks l s =
  Label.Tree.find blks l |>
  Option.value_map ~default:s ~f:(fun b ->
      match Blk.ctrl b with
      | `hlt | `ret _ -> s
      | `jmp d -> dst cpy blks s d
      | `br (_, y, n) ->
        dst cpy blks (dst cpy blks s y) n
      | `sw (_, _, d, tbl) ->
        let init = local cpy blks s d in
        Ctrl.Table.enum tbl |> Seq.fold ~init
          ~f:(fun s (_, l) -> local cpy blks s l))

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

let map_operand s (o : operand) : operand = match o with
  | `var x ->
    begin match Map.find s x with
      | None -> o
      | Some o -> o
    end
  | _ -> o

let map_local s (l : local) : local = match l with
  | `label (l, args) -> `label (l, List.map args ~f:(map_operand s))

let map_global s (g : global) : global = match g with
  | `var x ->
    begin match Map.find s x with
      | None -> g
      | Some `var x -> `var x
      | Some `int (a, _) -> `addr a
      | Some (`sym _ as s) -> s
      | Some _ -> assert false
    end
  | _ -> g

let map_dst s (d : dst) : dst = match d with
  | #local as l -> (map_local s l :> dst)
  | #global as g -> (map_global s g :> dst)

let map_sel s x t c l r =
  let c = match Map.find s c with
    | None -> c
    | Some `var c -> c
    | Some _ -> assert false in
  `sel (x, t, c, map_operand s l, map_operand s r)

let map_call s x f args vargs =
  let args = List.map args ~f:(map_operand s) in
  let vargs = List.map vargs ~f:(map_operand s) in
  `call (x, map_global s f, args, vargs)

let map_br s c y n =
  let c = match Map.find s c with
    | None -> c
    | Some `var c -> c
    | Some _ -> assert false in
  `br (c, map_dst s y, map_dst s n)

let map_sw s t i d tbl =
  let d = map_local s d in
  let tbl = Ctrl.Table.map_exn tbl ~f:(fun i l -> i, map_local s l) in
  match i with
  | `sym _ -> `sw (t, i, d, tbl)
  | `var x -> match Map.find s x with
    | None -> `sw (t, i, d, tbl)
    | Some (`var _ | `sym _ as i) -> `sw (t, i, d, tbl)
    | Some `int (i, _) ->
      let d =
        Ctrl.Table.find tbl i |>
        Option.value ~default:d in
      `jmp (d :> dst)
    | Some  _ -> assert false

let run fn =
  let s = analyze fn in
  if not @@ Map.is_empty s then
    let dst = map_dst s in
    let glo = map_global s in
    let oper = map_operand s in
    Func.map_blks fn ~f:(fun b ->
        Blk.map_insns b ~f:(fun _ -> function
            | `bop (x, b, l, r) -> `bop (x, b, oper l, oper r)
            | `uop (x, u, a) -> `uop (x, u, oper a)
            | `sel (x, t, c, l, r) -> map_sel s x t c l r
            | `call (x, f, args, vargs) -> map_call s x f args vargs
            | `load (x, t, a) -> `load (x, t, oper a)
            | `store (t, v, a) -> `store (t, oper v, oper a)
            | `vastart a -> `vastart (glo a)
            | `vaarg (x, t, a) -> `vaarg (x, t, glo a)) |>
        Blk.map_ctrl ~f:(function
            | `hlt -> `hlt
            | `ret None as r -> r
            | `ret Some x -> `ret (Some (oper x))
            | `jmp d -> `jmp (dst d)
            | `br (c, y, n) -> map_br s c y n
            | `sw (t, i, d, tbl) -> map_sw s t i d tbl))

  else fn
