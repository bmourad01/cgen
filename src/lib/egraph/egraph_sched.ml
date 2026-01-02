(* Track the provenance between e-class IDs and labels in the CFG
   representation. This gets mainly used for the purpose of code
   motion when we extract back to the CFG form. *)

open Core
open Egraph_common
open Virtual

(* Resolve both labels to their corresponding blocks before we
   walk up the tree. *)
let lca t a b =
  let reso = Resolver.resolve t.input.reso in
  match reso a, reso b with
  | None, _ | _, None -> assert false
  | Some (`insn (_, ba, _, _) | `blk ba),
    Some (`insn (_, bb, _, _) | `blk bb) ->
    Semi_nca.Tree.lca_exn t.input.dom (Blk.label ba) (Blk.label bb)

(* Note that `id` must be the canonical e-class. *)
let move t old l id =
  Logs.debug (fun m ->
      let pp_old ppf old =
        if List.is_empty old
        then Format.fprintf ppf ""
        else Format.fprintf ppf "from %s "
            (List.to_string ~f:Label.to_string old) in
      m "%s: moving term %d %ato %a%!"
        __FUNCTION__ id pp_old old Label.pp l);
  add_moved t id old;
  set_label t id l;
  Hashtbl.update t.lmoved l ~f:(function
      | None -> Iset.singleton id
      | Some s -> Iset.add s id)

let mark_use t id a =
  Logs.debug (fun m -> m "%s: id=%d, a=%a%!" __FUNCTION__ id Label.pp a);
  add_moved t id [a]

(* Update when we union two nodes together. Should not be
   called if both IDs are the same. *)
let merge t a b u =
  assert (a <> b);
  let cid = find t a in
  (* Link the ID to the label, along with the union ID. *)
  let link ?p dir l =
    Logs.debug (fun m ->
        m "%s: merge dominated %s: a=%d, b=%d, cid=%d, u=%d, l=%a, p=%a%!"
          __FUNCTION__
          (match dir with `left -> "left" | `right -> "right")
          a b cid u Label.pp l
          (Format.pp_print_option
             ~none:(fun ppf () -> Format.fprintf ppf "<none>")
             Label.pp) p);
    Option.iter p ~f:(mark_use t cid);
    set_label t cid l;
    set_label t u l in
  match labelof t a, labelof t b with
  | None, None -> ()
  | None, Some pb -> link `right pb
  | Some pa, None -> link `left pa
  | Some pa, Some pb when Label.(pa = pb) -> ()
  | Some pa, Some pb when dominates t ~parent:pb pa -> link `right pb ~p:pa
  | Some pa, Some pb when dominates t ~parent:pa pb -> link `left pa ~p:pb
  | Some pa, Some pb ->
    let pc = lca t pa pb in
    Logs.debug (fun m ->
        m "%s: merge LCA: a=%d, b=%d, cid=%d, u=%d, pa=%a, pb=%a, pc=%a%!"
          __FUNCTION__ a b cid u Label.pp pa Label.pp pb Label.pp pc);
    assert (cid = find t b);
    assert (cid = find t u);
    clear_label t a;
    clear_label t b;
    move t [pa; pb] pc cid

let rec useof t l : enode -> unit = function
  | U {pre; post} ->
    mark_use t pre l;
    mark_use t post l;
    useof t l @@ node t pre;
    useof t l @@ node t post
  | N (_, cs) ->
    List.iter cs ~f:(fun c ->
        mark_use t c l;
        useof t l @@ node t c)

let default_placement t id l n =
  Logs.debug (fun m ->
      m "%s: placing term %d at %a:\n  node: %a%!"
        __FUNCTION__ id Label.pp l
        (Enode.pp ~node:(node t)) n);
  move t [] l id;
  useof t l n

(* We've matched on a value that we already hash-consed, so
   figure out which label it should correspond to. *)
let duplicate t id a =
  let cid = find t id in
  match labelof t cid with
  | Some b when Label.(b = a) -> ()
  | Some b when dominates t ~parent:b a ->
    Logs.debug (fun m ->
        m "%s: %d at %a dominated by previous term %d at %a%!"
          __FUNCTION__ id Label.pp a cid Label.pp b);
    mark_use t cid a
  | Some b when dominates t ~parent:a b ->
    Logs.debug (fun m ->
        m "%s: %d at %a dominates previous term %d at %a%!"
          __FUNCTION__ id Label.pp a cid Label.pp b);
    mark_use t cid b;
    set_label t id a
  | Some b ->
    let c = lca t a b in
    Logs.debug (fun m ->
        m "%s: %d at %a LCA with previous term %d at %a: %a%!"
          __FUNCTION__ id Label.pp a cid Label.pp b Label.pp c);
    clear_label t cid;
    move t [a; b] c cid;
  | None ->
    Logs.debug (fun m ->
        m "%s: %d at %a has no previous term, cid=%d%!"
          __FUNCTION__ id Label.pp a cid);
    (* This e-class wasn't moved, though it wasn't registered
       to begin with (even though it was hash-consed). *)
    default_placement t id a @@ node t id

module Licm = struct
  let header t lp = Loops.(header @@ get t.input.loop lp)
  let is_child_loop ~parent t a = Loops.is_child_of ~parent t.input.loop a
  let find_blk_loop t l = Loops.blk t.input.loop l

  let find_loop t l = match Resolver.resolve t.input.reso l with
    | Some (`blk b | `insn (_, b, _, _)) ->
      find_blk_loop t @@ Blk.label b
    | None -> assert false

  module Variance = struct
    (* Almost the same as `child`, but ignores the special cases
       thereof. *)
    let rec is_variant ~lp t l n = match find_loop t l with
      | Some lp' when Loops.equal_loop lp lp' -> true
      | Some lp' when is_child_loop ~parent:lp' t lp -> false
      | Some _ -> children ~lp t n
      | None -> false

    (* Same as below, but we examine just the children of `n`. *)
    and children ~lp t n = match (n : enode) with
      | N (_, cs) -> List.exists cs ~f:(child ~lp t)
      | U {pre; post} ->
        (* We will take a conservative approach here. Since we can't
           predict whether the rewritten term is the one that will
           be extracted, we have to consider whether either terms are
           loop-variant. *)
        let go = Fn.compose (children ~lp t) (node t) in
        go pre || go post

    (* Generic entry point for determining of a node ID is variant
       w.r.t the loop `lp`.

       This has a lot of comments in an effort to convince myself
       that this is correct.
    *)
    and child ~lp t id = match node t id with
      | N (Ovar x, []) ->
        (* The node is a "free" variable, so it's restricted to a
           few scenarios, mainly related to whether it's an induction
           variable of the current loop or not. *)
        begin match Resolver.def t.input.reso x with
          | Some (`slot | `arg) ->
            (* Arguments and stack slots have scope for the entire
               function. *)
            false
          | Some `blkarg b ->
            (* It's block argument, so find out if it belongs to a
               loop. *)
            begin match find_blk_loop t @@ Blk.label b with
              | Some lp' when Loops.equal_loop lp lp' ->
                (* It's defined by a block within the current loop. *)
                true
              | Some lp' when is_child_loop ~parent:lp' t lp ->
                (* The current loop is nested inside of the one that
                   the node is defined in. *)
                false
              | Some lp' when is_child_loop ~parent:lp t lp' ->
                (* It's defined in a loop that is a child of the
                   current one. *)
                true
              | Some _ ->
                (* It's defined in a loop, but not a child, nor a parent,
                   of the current one. *)
                false
              | None ->
                (* It's not defined inside of any loop, so it's
                   invariant. *)
                false
            end
          | Some _ ->
            (* It's defined by some instruction that we can't move. *)
            true
          | None -> assert false
        end
      | n when Enode.is_const n ->
        (* If it's a constant then it is definitely invariant. *)
        false
      | n -> match labelof t id with
        | Some l ->
          (* Ask if where the node lives is variant with respect to
             the current loop. *)
          is_variant ~lp t l n
        | None ->
          (* We don't know where this node was defined or moved to,
             so we will play it safe and consider it variant. *)
          true
  end

  let header_parent t lp =
    header t lp |> Semi_nca.Tree.parent t.input.dom |> Option.value_exn

  let partition_uses t x =
    Resolver.uses t.input.reso x |>
    List.partition_map ~f:(function
        | `blk b | `insn (_, b, _, _) ->
          let l = Blk.label b in
          match find_blk_loop t l with
          | None -> First l
          | Some lp -> Second lp)

  let exists_in_loop t parent = List.exists ~f:(is_child_loop ~parent t)

  let licm_move t l l' lp id lhs =
    Logs.debug (fun m ->
        m "%s: LICM for term %d: l=%a, l'=%a:\n  loop: %a\n  node: %a%!"
          __FUNCTION__ id Label.pp l Label.pp l'
          Loops.pp_data (Loops.get t.input.loop lp)
          (Enode.pp ~node:(node t)) (node t id));
    let l' = match lhs with
      | None -> l'
      | Some x -> match partition_uses t x with
        | [], [] -> l'
        | init :: xs, [] ->
          (* Never used inside of a loop. *)
          List.fold xs ~init ~f:(lca t)
        | _, ys when exists_in_loop t lp ys ->
          (* Pin at the current label if it's used in one of the
             loops we just hoisted out of. *)
          set_pinned t id;
          l'
        | xs, init :: ys ->
          (* Otherwise, find the common ancestor. *)
          set_pinned t id;
          let init = header_parent t init in
          List.fold ys ~init ~f:(fun acc lp ->
              lca t acc @@ header_parent t lp) |> fun init ->
          List.fold xs ~init ~f:(lca t) in
    move t [l] l' id

  (* We've determined that `n` is invariant with respect to `lp`, but
     if `lp` is nested in a parent loop `lp'`, then we should find out if
     `n` is also invariant with respect to `lp'`, and so on. *)
  let rec licm' t l n lp id lhs =
    let l' = header_parent t lp in
    match find_blk_loop t l' with
    | None -> licm_move t l l' lp id lhs
    | Some lp' ->
      if Variance.children ~lp:lp' t n
      then licm_move t l l' lp id lhs
      else licm' t l n lp' id lhs

  let licm t l n lp id lhs =
    if Variance.children ~lp t n
    then default_placement t id l n
    else licm' t l n lp id lhs
end

(* Verify that a div/rem instruction may trap. *)
let check_div_rem t : enode -> bool = function
  | N (Obinop (`div #Type.imm | `udiv _ | `rem #Type.imm | `urem _), [_; r]) ->
    begin match node t r with
      | N (Oint (i, _), []) -> Bv.(i = zero)
      | _ -> true
    end
  | _ -> false

let is_effectful t n i =
  Insn.can_load i ||
  Insn.is_effectful i ||
  check_div_rem t n

(* Track the provenance between the node and the label, but first see
   if we can do LICM (loop-invariant code motion). *)
let add t l id n = match Resolver.resolve t.input.reso l with
  | None -> assert false
  | Some `blk _ -> default_placement t id l n
  | Some `insn (i, _, _, _) when is_effectful t n i ->
    default_placement t id l n
  | Some `insn (_, b, lhs, _) ->
    match Licm.find_blk_loop t @@ Blk.label b with
    | None -> default_placement t id l n
    | Some lp -> Licm.licm t l n lp id lhs
