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

  let search t p id =
    let subst env x term = Map.update env x ~f:(function
        | Some term' when S.equal_term Rv.equal term term' -> term
        | Some _ -> raise_notrace Mismatch
        | None -> term) in
    let regvar env x r id k = match typeof t id with
      | Some (#Type.basic as ty) ->
        k @@ subst env x @@ S.Regvar (r, ty)
      | Some _ | None -> raise_notrace Mismatch in
    let rec go env p id k = match (p : P.t) with
      | P (x, xs) -> pat env x xs id k
      | V x -> var env x id k
      | C (x, ty) -> constant env x ty id k
    and pat env x xs id k = match node t id with
      | N (y, ys) when P.equal_op x y -> children env xs ys k
      | N _ | Rv _ -> raise_notrace Mismatch
    and var env x id k = match node t id with
      | N (Oaddr a, []) -> k @@ subst env x @@ S.Imm (a, wordi)
      | N (Obool b, []) -> k @@ subst env x @@ S.Bool b
      | N (Odouble d, []) -> k @@ subst env x @@ S.Double d
      | N (Oint (i, ty), []) -> k @@ subst env x @@ S.Imm (i, ty)
      | N (Osingle s, []) -> k @@ subst env x @@ S.Single s
      | N (Osym (s, o), []) -> k @@ subst env x @@ S.Sym (s, o)
      | N (Olocal l, []) -> k @@ subst env x @@ S.Label l
      | Rv r -> regvar env x r id k
      | N _ -> match Hashtbl.find t.id2r id with
        | None -> raise_notrace Mismatch
        | Some r -> regvar env x r id k
    and constant env x ty id k = match ty, node t id with
      | (#Type.imm_base as ti), N (Oaddr a, [])
        when Type.equal_imm_base ti word ->
        k @@ subst env x @@ S.Imm (a, wordi)
      | `i8, N (Oint (i, `i8), []) -> k @@ subst env x @@ S.Imm (i, `i8)
      | `i16, N (Oint (i, `i16), []) -> k @@ subst env x @@ S.Imm (i, `i16)
      | `i32, N (Oint (i, `i32), []) -> k @@ subst env x @@ S.Imm (i, `i32)
      | `i64, N (Oint (i, `i64), []) -> k @@ subst env x @@ S.Imm (i, `i64)
      | `f64, N (Odouble d, []) -> k @@ subst env x @@ S.Double d
      | `f32, N (Osingle s, []) -> k @@ subst env x @@ S.Single s
      | `sym, N (Osym (s, o), []) -> k @@ subst env x @@ S.Sym (s, o)
      | _ -> raise_notrace Mismatch
    and children env xs ys k = match List.zip xs ys with
      | Unequal_lengths -> raise_notrace Mismatch
      | Ok l -> child env k l
    and child env k = function
      | [] -> k env
      | [p, id] -> go env p id k
      | (p, id) :: xs ->
        go env p id @@ fun env ->
        child env k xs in
    go S.empty p id Base.Fn.id

  let match_one t id pre post =
    try Some (search t pre id, post) with
    | Mismatch -> None

  let insns t l = match Hashtbl.find t.insn l with
    | None -> !![]
    | Some ids ->
      Ftree.to_list ids |> C.List.map ~f:(fun id ->
          C.List.find_map I.rules ~f:(fun r ->
              try
                let pre, post = (r :> (Rv.t, M.Insn.t) R.t) in
                post @@ search t pre id
              with Mismatch -> !!None)
          >>| Option.value ~default:[])
      >>| List.concat

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
    compare (t.rpo @@ Blk.label b) (t.rpo @@ Blk.label a)

  let run t =
    let+ blks =
      Func.blks t.fn |>
      C.Seq.map ~f:(step t) >>|
      Seq.to_list in
    Pseudo.Func.create ~name:(Func.name t.fn) ~blks
end
