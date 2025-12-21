(** Adapted from the paper:

    "Tilting at windmills with Coq: formal verification of a
    compilation algorithm for parallel moves" (2008)

    by L. Rideau, B. P. Serpette, & X. Leroy
*)

open Core
open Monads.Std
open Regular.Std

module Make(C : Context_intf.S) = struct
  open C.Syntax

  let windmill t l moves ~emit =
    let moves = Array.of_list moves in
    let n = Array.length moves in
    let status = Array.create ~len:n `to_move in
    let subst = Var.Table.create () in
    let rewrite = function
      | `var v as default ->
        Hashtbl.find subst v |>
        Option.value ~default
      | src -> src in
    let emit ?i dst src =
      let+ () = emit dst @@ rewrite src in
      Option.iter i ~f:(fun i -> status.(i) <- `moved) in
    let rec move_one i =
      let dst, src = moves.(i) in
      match src with
      | #Virtual.const ->
        (* Not a var: emit normally. *)
        emit ~i dst src
      | `var v when Var.(dst = v) ->
        (* Ignore redundant moves. *)
        !!(status.(i) <- `moved)
      | `var _ ->
        status.(i) <- `being_moved;
        let* () = dfs i dst in
        emit ~i dst src
    and dfs i dst = Seq.range 0 n |> C.Seq.iter ~f:(fun j ->
        (* Find a child whose `src` depends on `dst`. *)
        C.unless (i = j) @@ fun () ->
        match rewrite @@ snd moves.(j) with
        | #Virtual.const -> !!()
        | `var v when Var.(dst <> v) -> !!()
        | `var v as src' -> match status.(j) with
          | `moved -> !!()
          | `to_move -> move_one j
          | `being_moved ->
            (* Found a cycle, so we need to use a fresh
               temporary. *)
            let* tmp = C.Var.fresh in
            let+ () = emit tmp src' in
            (* Any future mention of `v` will refer to `tmp`. *)
            Hashtbl.set subst ~key:v ~data:(`var tmp)) in
    (* Entry point: consider all pending moves. *)
    Seq.range 0 n |> C.Seq.iter ~f:(fun i ->
        match status.(i) with
        | `to_move -> move_one i
        | _ -> !!())
end
