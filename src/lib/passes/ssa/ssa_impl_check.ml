open Core
open Regular.Std
open Graphlib.Std
open Ssa_impl_common

(* Verify that the function does not violate the SSA invariants. *)
module Make(M : L) : sig
  val go : Label.t tree -> M.Func.t -> unit
end = struct
  open M

  let fail fn = failwithf "$%s violates SSA invariants" (Func.name fn) ()

  let check_dom ?(k = Fn.id) dom fn b b' =
    let l = Blk.label b in
    let l' = Blk.label b' in
    if Label.(l = l') then k ()
    else if not (Tree.is_descendant_of dom ~parent:l l')
    then fail fn

  (* The resolver should handle multiple definitions, as well as uses
     with no definitions. Our remaining task is to check that each
     definition dominates its uses. *)
  let go dom fn = match Resolver.create fn with
    | Error err -> failwith @@ Error.to_string_hum err
    | Ok r -> Func.blks fn |> Seq.iter ~f:(fun b ->
        Blk.args b |> Seq.iter ~f:(fun x ->
            Resolver.uses r x |> List.iter ~f:(function
                | `insn (_, b', _, _) | `blk b' ->
                  check_dom dom fn b b'));
        Blk.insns b |> Seq.iteri ~f:(fun ord i ->
            Insn.lhs i |> List.iter ~f:(fun x ->
                Resolver.uses r x |> List.iter ~f:(function
                    | `blk b' -> check_dom dom fn b b'
                    | `insn (_, b', _,  ord') ->
                      check_dom dom fn b b' ~k:(fun () ->
                          (* Check that `i` is defined before `i'`. *)
                          if ord >= ord' then fail fn)))))
end
