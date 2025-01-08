open Core
open Regular.Std
open Virtual.Abi
open Isel_common

module S = Isel_internal.Subst
module P = Isel_internal.Pattern

module Make(M : Machine_intf.S)(C : Context_intf.S) = struct
  open C.Syntax

  module I = M.Isel(C)
  module R = Isel_internal.Rule(C)
  module Rv = M.Regvar

  exception Mismatch

  let word = Target.word M.target
  let wordi = (word :> Type.imm)

  type rule = (Rv.t, M.Insn.t) R.t
  type env = Rv.t S.t
  type k = env -> env

  let search t p id =
    let subst env x term = Map.update env x ~f:(function
        | Some term' when S.equal_term Rv.equal term term' -> term
        | Some _ -> raise_notrace Mismatch
        | None -> term) in
    let regvar env x r id k = match typeof t id with
      | Some (#Type.basic as ty) ->
        k @@ subst env x @@ Regvar (r, ty)
      | Some _ | None -> raise_notrace Mismatch in
    let rec go : type a b. env -> (a, b) P.t -> id -> k -> env =
      fun env p id k -> match p with
        | P (x, xs) -> pat env x xs id k
        | V x -> var env x id k
    and pat : type b c. env -> P.op -> (b, c) P.t list -> id -> k -> env =
      fun env x xs id k ->  match node t id with
        | N (y, ys) when P.equal_op x y -> children env xs ys k
        | N _ | Rv _ -> raise_notrace Mismatch
    and var env x id k = match node t id with
      | N (Oaddr a, []) -> k @@ subst env x @@ Imm (a, wordi)
      | N (Obool b, []) -> k @@ subst env x @@ Bool b
      | N (Odouble d, []) -> k @@ subst env x @@ Double d
      | N (Oint (i, ty), []) -> k @@ subst env x @@ Imm (i, ty)
      | N (Osingle s, []) -> k @@ subst env x @@ Single s
      | N (Osym (s, o), []) -> k @@ subst env x @@ Sym (s, o)
      | N (Olocal l, []) -> k @@ subst env x @@ Label l
      | Rv r -> regvar env x r id k
      | N _ -> match Hashtbl.find t.id2r id with
        | None -> raise_notrace Mismatch
        | Some r -> regvar env x r id k
    and children : type b c. env -> (b, c) P.t list -> id list -> k -> env =
      fun env xs ys k -> match List.zip xs ys with
        | Unequal_lengths -> raise_notrace Mismatch
        | Ok l -> child env k l
    and child : type b c. env -> k -> ((b, c) P.t * id) list -> env =
      fun env k -> function
        | [] -> k env
        | [p, id] -> go env p id k
        | (p, id) :: xs ->
          go env p id @@ fun env ->
          child env k xs in
    go S.empty p id Base.Fn.id

  let match_one t id =
    let rules = (I.rules :> rule list) in
    C.List.find_map rules ~f:(function
        | _, [] -> !!None
        | pre, posts -> match search t pre id with
          | exception Mismatch -> !!None
          | env -> C.List.find_map posts ~f:((|>) env))
    >>| Option.value ~default:[]

  let insns t l = match Hashtbl.find t.insn l with
    | None -> !![]
    | Some ids ->
      Ftree.to_list ids |>
      C.List.map ~f:(match_one t) >>|
      List.concat

  let step t b =
    let label = Blk.label b in
    let* init = insns t label in
    let+ insns =
      Blk.insns b ~rev:true |>
      C.Seq.fold ~init ~f:(fun acc i ->
          let+ insns = insns t @@ Insn.label i in
          insns @ acc) in
    Pseudo.Blk.create ~label ~insns

  let compare_postorder t a b =
    let a = Blk.label a in
    let b = Blk.label b in
    compare (t.rpo b) (t.rpo a)

  let run t =
    let+ blks =
      Func.blks t.fn |> Seq.to_list |>
      List.sort ~compare:(compare_postorder t) |>
      C.List.fold ~init:[] ~f:(fun acc b ->
          step t b >>| Fn.flip List.cons acc) in
    Pseudo.Func.create ~name:(Func.name t.fn) ~blks
end
