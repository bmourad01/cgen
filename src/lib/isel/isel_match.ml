open Core
open Regular.Std
open Virtual.Abi
open Isel_common

module Make(M : Machine_intf.S)(C : Context_intf.S) = struct
  open C.Syntax

  module I = M.Isel(C)
  module R = Isel_internal.Rule(C)
  module Rv = M.Regvar

  exception Mismatch

  let word = Target.word M.target
  let wordi = (word :> Type.imm)
  let wordb = (word :> Type.basic)

  type rule = (Rv.t, M.Insn.t) R.t
  type callback = (Rv.t, M.Insn.t) R.callback
  type env = Rv.t S.t
  type k = env -> env

  let pp_node t = pp_node t Rv.pp

  type pat =
    | V1 of string
    | P1 of P.op * pat list

  let rec pp_pat ppf = function
    | V1 x -> Format.fprintf ppf "?%s" x
    | P1 (op, []) -> Format.fprintf ppf "%a" P.pp_op op
    | P1 (op, ps) ->
      let pp_sep ppf () = Format.fprintf ppf " " in
      Format.fprintf ppf "(%a %a)"
        P.pp_op op
        (Format.pp_print_list ~pp_sep pp_pat)
        ps

  let rec to_untyped : type a b. (a, b) P.t -> pat = function
    | P (op, ps) -> P1 (op, List.map ps ~f:to_untyped)
    | V x -> V1 x

  type tables = {
    moves : (P.op, (pat * pat list * callback list) seq) Hashtbl.t;
    other : (P.op, (pat list * callback list) seq) Hashtbl.t;
  }

  (* Reduce the search space by specializing the top-level pattern
     for each rule's LHS. It stands to reason that we will have many
     rules but only a handful of them will match with any given node. *)
  let build_tables (rules : rule list) =
    let module Op = struct
      type t = P.op [@@deriving compare, hash, sexp]
    end in
    let ts = {
      moves = Hashtbl.create (module Op);
      other = Hashtbl.create (module Op);
    } in
    (* We'll store it as a sequence since it will be modified on-demand
       during the search. *)
    let update t k a = Hashtbl.update t k ~f:(function
        | Some s -> Seq.(append s @@ singleton a)
        | None -> Seq.singleton a) in
    List.iter rules ~f:(fun (pre, post) ->
        match to_untyped pre with
        | P1 (Omove, [a; P1 (op, ps)]) ->
          update ts.moves op (a, ps, post)
        | P1 (op, ps) ->
          update ts.other op (ps, post)
        | V1 _ -> assert false);
    ts

  let rules = (I.rules :> rule list)
  let tables = build_tables rules

  let commutable = function
    | P.Obinop b ->
      begin match b with
        | `add _
        | `mul _
        | `mulh _
        | `umulh _
        | `and_ _
        | `or_ _
        | `xor _
        | `eq _
        | `ne _ -> true
        | _ -> false
      end
    | _ -> false

  (* The actual tree-matching routine, which builds up a substitution
     for the LHS of a rule, for consumption by the callbacks on the RHS. *)
  let search t =
    let subst env id x term = Map.update env x ~f:(function
        | Some i when i.S.id = id ->
          assert (S.equal_term Rv.equal i.tm term); i
        | Some _ -> raise_notrace Mismatch
        | None -> S.{id; tm = term}) in
    let regvar env x r id k = match typeof t id with
      | Some (#Type.basic as ty) ->
        k @@ subst env id x @@ Regvar (r, ty)
      | Some `v128 ->
        k @@ subst env id x @@ Regvar_v r
      | Some `flag ->
        k @@ subst env id x @@ Regvar (r, wordb)
      | None -> raise_notrace Mismatch in
    let rec go env p id k = match p with
      | P1 (x, xs) -> pat env x xs id k
      | V1 x -> var env x id k
    and pat env x xs id k = match node t id with
      | N (y, ys) when P.equal_op x y ->
        (* If it fails initially, see if commuting the operands will produce
           a match. This should cut down on the number of cases we have to
           cover in our patterns. *)
        begin try children env xs ys k with
          | Mismatch when commutable x ->
            children env xs (List.rev ys) k
        end
      | N _ | Rv _ | Tbl _ -> raise_notrace Mismatch
    and var env x id k = match node t id with
      | N (Oaddr a, []) -> k @@ subst env id x @@ Imm (a, wordi)
      | N (Obool b, []) -> k @@ subst env id x @@ Bool b
      | N (Odouble d, []) -> k @@ subst env id x @@ Double d
      | N (Oint (i, ty), []) -> k @@ subst env id x @@ Imm (i, ty)
      | N (Osingle s, []) -> k @@ subst env id x @@ Single s
      | N (Osym (s, o), []) -> k @@ subst env id x @@ Sym (s, o)
      | N (Olocal l, []) -> k @@ subst env id x @@ Label l
      | Tbl (d, tbl) -> k @@ subst env id x @@ Table (d, tbl)
      | Rv r -> regvar env x r id k
      | N _ -> match Hashtbl.find t.id2r id with
        | None -> raise_notrace Mismatch
        | Some r -> regvar env x r id k
    and children env xs ys k = match List.zip xs ys with
      | Unequal_lengths -> raise_notrace Mismatch
      | Ok l -> child env k l
    and child env k = function
      | [] -> k env
      | [p, id] -> go env p id k
      | (p, id) :: xs ->
        go env p id @@ fun env ->
        child env k xs in
    (fun env p id -> go env p id Base.Fn.id),
    (fun env xs ys -> children env xs ys Base.Fn.id)

  (* The most general rule `move ?x ?y` needs to exclude cases where ?x and
     ?y refer to the same term, otherwise we will mistakenly achieve coverage
     with an incorrect instruction lowering.

     These cases occur because of how the DAG gets built. ?x may refer to the
     result of computing ?y because future instructions may want to match on
     it.
  *)
  let is_blank_move env = function
    | [V1 x; V1 y] ->
      begin match Map.find env x, Map.find env y with
        | Some x, Some y ->
          let open S in
          (* This usually isn't the case, but doesn't hurt to check. *)
          x.id = y.id ||
          (* They might end up having different IDs, but this should
             catch the edge cases. *)
          equal_term Rv.equal x.tm y.tm
        | _ -> false
      end
    | _ -> false

  let fail_match t l id =
    C.failf "In Isel_match.match_one: at label %a in function $%s: \
             failed to produce instructions for node %a (id %d)"
      Label.pp l (Func.name t.fn) (pp_node t) id id ()

  (* Find the appropriate rules to match against based on the top-level
     operator of the current node. *)
  let fetch_rules t l id =
    let default op cs = match Hashtbl.find tables.other op with
      | None -> fail_match t l id
      | Some tls -> Seq.map tls ~f:(fun (ps, posts) ->
          None, (cs, ps), posts) |> C.return in
    match node t id with
    | N (Omove, [a; b]) ->
      begin match node t b with
        | N (op, cs) ->
          begin match Hashtbl.find tables.moves op with
            | None -> default Omove [a; b]
            | Some tls -> Seq.map tls ~f:(fun (pa, ps, posts) ->
                Some (a, pa, op), (cs, ps), posts) |> C.return
          end
        | Rv _ -> default Omove [a; b]
        | _ -> fail_match t l id
      end
    | N (op, cs) -> default op cs
    | _ -> fail_match t l id

  let match_one t l id =
    let* rules = fetch_rules t l id in
    let go, children = search t in
    C.Seq.find_map rules ~f:(function
        | _, _, [] -> !!None
        | p, (cs, ps), posts ->
          try
            let env, comm = match p with
              | None -> S.empty, false
              | Some (c, p, op) ->
                (* Do the match first before checking commutativity. *)
                let env = go S.empty p c in
                env, commutable op in
            let env = try children env ps cs with
              | Mismatch when comm ->
                children env ps @@ List.rev cs in
            if Option.is_none p && is_blank_move env ps
            then raise_notrace Mismatch;
            R.try_ env posts
          with Mismatch -> !!None) >>= function
    | None -> fail_match t l id
    | Some is -> !!is

  let insns t l = match Hashtbl.find t.insn l with
    | None -> !![]
    | Some ids ->
      Ftree.to_list ids |>
      C.List.map ~f:(match_one t l) >>|
      List.concat

  let freshen = C.List.map ~f:(fun i ->
      let+ label = C.Label.fresh in
      Pseudo.Insn.create ~label ~insn:i)

  let step t b =
    let label = Blk.label b in
    let* extra = match Hashtbl.find t.extra label with
      | None -> !![]
      | Some ls ->
        (* NB: we're reversing the order on purpose. *)
        C.List.fold ls ~init:[] ~f:(fun acc l ->
            let+ insns = insns t l >>= freshen in
            Pseudo.Blk.create ~label:l ~insns :: acc) in
    let* init = insns t label >>= freshen in
    let+ insns =
      Blk.insns b ~rev:true |>
      C.Seq.fold ~init ~f:(fun acc i ->
          let+ insns = insns t (Insn.label i) >>= freshen in
          insns @ acc) in
    Pseudo.Blk.create ~label ~insns :: extra

  let compare_postorder t a b =
    let a = Blk.label a in
    let b = Blk.label b in
    compare (t.rpo b) (t.rpo a)

  let transl_blks t =
    Func.blks t.fn |> Seq.to_list |>
    List.sort ~compare:(compare_postorder t) |>
    C.List.fold ~init:[] ~f:(fun acc b ->
        step t b >>| Fn.flip List.cons acc)
    >>| List.concat

  let transl_rets t =
    Func.blks t.fn |> C.Seq.fold ~init:[] ~f:(fun acc b ->
        match Blk.ctrl b with
        | `ret rets ->
          C.List.fold rets ~init:acc ~f:(fun acc (r, _) ->
              match M.Reg.of_string r with
              | Some r -> !!(r :: acc)
              | None ->
                C.failf
                  "In Isel_match.transl_rets: %s is not a valid register"
                  r ())
        | _ -> !!acc)
    >>| List.dedup_and_sort ~compare:M.Reg.compare

  let run t =
    let* blks = transl_blks t in
    let* rets = transl_rets t in
    let dict = if t.frame
      then Dict.singleton Pseudo.Func.Tag.needs_stack_frame ()
      else Dict.empty in
    C.lift_err @@ Pseudo.Func.create ()
      ~name:(Func.name t.fn)
      ~slots:(Func.slots t.fn |> Seq.to_list)
      ~dict ~blks ~rets
end
