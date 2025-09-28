open Core
open Regular.Std
open Ssa_impl_common

(* Verify that the function does not violate the SSA invariants. *)
module Make(M : L) : sig
  val go : Label.t Semi_nca.tree -> M.Func.t -> unit
end = struct
  open M

  let fail fn msg =
    failwithf "$%s violates SSA invariants: %s"
      (Func.name fn) msg ()

  let check_dom ?(k = Fn.id) dom fn b b' =
    let l = Blk.label b in
    let l' = Blk.label b' in
    if Label.(l = l') then k ()
    else if not (Semi_nca.Tree.is_descendant_of dom ~parent:l l')
    then fail fn "dominance check failed"

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
                          if ord >= ord' then
                            fail fn @@ Format.asprintf
                              "use before definition of %a"
                              Var.pp x)))))
end
