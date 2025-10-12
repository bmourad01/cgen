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

  let pp_node t = pp_node t Rv.pp

  let rules = (I.rules :> rule list)

  module Matcher = Matcher.Make(struct
      type op = P.op [@@deriving compare, equal, hash, sexp]
      type term = Rv.t node
      type id = Id.t [@@deriving equal]

      let is_commutative = function
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

      let term_op = function
        | N (o, _) -> Some o
        | Rv _ | Tbl _ | Callargs _ -> None

      let term_args = function
        | N (_, args) -> args
        | Rv _ | Tbl _ | Callargs _ -> []

      let term_union _ = None

      let pp_id = Id.pp
      let pp_op = P.pp_op
    end)

  module VM = Matcher.VM
  module Y = Matcher.Yield

  let prog, vm =
    (* XXX: don't try this at home! The representations are exactly the
       same, but we need to erase the type constraints on the input. *)
    let to_untyped p = (Obj.magic p : Matcher.pat) in
    let pats = List.map rules ~f:(fun (p, cbs) -> to_untyped p, cbs) in
    let prog = Matcher.compile pats ~commute:true in
    prog, VM.create ()

  (* Translate a substitution we got from the matcher
     into one that our rule callbacks can understand. *)
  let map_subst_terms t (s : Matcher.subst) : Rv.t S.t =
    let open S in
    let regvar id r = match typeof t id with
      | Some (#Type.basic as ty) -> Regvar (r, ty)
      | Some `v128 -> Regvar_v r
      | Some `flag -> Regvar (r, wordb)
      | None -> raise_notrace Mismatch in
    Map.map s ~f:(fun id ->
        let tm = match node t id with
          | N (Oaddr a, []) -> Imm (a, wordi)
          | N (Obool b, []) -> Bool b
          | N (Odouble d, []) -> Double d
          | N (Oint (i, ty), []) -> Imm (i, ty)
          | N (Osingle s, []) -> Single s
          | N (Osym (s, o), []) -> Sym (s, o)
          | N (Olocal l, []) -> Label l
          | Callargs rs -> Callargs rs
          | Tbl (d, tbl) -> Table (d, tbl)
          | Rv r -> regvar id r
          | N _ -> match Hashtbl.find t.id2r id with
            | None -> raise_notrace Mismatch
            | Some r -> regvar id r in
        S.{id; tm})

  let fail_init_matcher t l id =
    C.failf "In Isel_match.match_one: at label %a in function $%s: \
             failed to initialize matcher for node %a (id %d)"
      Label.pp l (Func.name t.fn) (pp_node t) id id

  let fail_match t l id =
    C.failf "In Isel_match.match_one: at label %a in function $%s: \
             failed to produce instructions for node %a (id %d)"
      Label.pp l (Func.name t.fn) (pp_node t) id id

  (* The most general rule `move ?x ?y` needs to exclude cases where ?x and
     ?y refer to the same term, otherwise we will mistakenly achieve coverage
     with an incorrect instruction lowering.

     These cases occur because of how the DAG gets built. ?x may refer to the
     result of computing ?y because future instructions may want to match on
     it.
  *)
  let check_blank_move s n (p : Matcher.pat) = match n, p with
    | N (Omove, [_; _]),
      P (Omove, [V x; V y]) ->
      begin match Map.(find s x, find s y) with
        | Some x, Some y
          when x.S.id = y.S.id
            || S.equal_term Rv.equal x.tm y.tm ->
          raise_notrace Mismatch
        | _ -> ()
      end
    | _ -> ()

  let match_one t l id =
    let init = VM.init ~lookup:(node t) vm prog id in
    let* () = C.unless init @@ fail_init_matcher t l id in
    let rec loop () = match VM.one vm prog with
      | None -> !!None
      | Some y ->
        try
          let s = map_subst_terms t @@ Y.subst y in
          check_blank_move s (node t id) @@ Y.pat y;
          R.try_ s (Y.payload y) >>= function
          | Some _ as is -> !!is
          | None -> loop ()
        with Mismatch -> loop () in
    loop () >>= function
    | None -> fail_match t l id ()
    | Some is -> !!is

  (* NB: the list we get from `t.insn` is in reverse order, so a normal
     fold will correct it. *)
  let insns t l = match Hashtbl.find t.insn l with
    | None -> !![]
    | Some ids -> C.List.fold ids ~init:[] ~f:(fun acc id ->
        let+ insns = match_one t l id in
        insns @ acc)

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
          let label = Insn.label i in
          let+ insns = insns t label >>= function
            | [] -> !![]
            | x :: xs ->
              let x = Pseudo.Insn.create ~label ~insn:x in
              let+ xs = freshen xs in
              x :: xs in
          insns @ acc) in
    Pseudo.Blk.create ~label ~insns :: extra

  (* Traverse the blocks in pseudo-postorder, which ends up accumulating
     in reverse postoder. *)
  let transl_blks t =
    Func.blks t.fn |> Seq.map ~f:(fun b -> b, t.rpo (Blk.label b)) |>
    Seq.to_list |> List.sort ~compare:(fun (_, a) (_, b) -> compare b a) |>
    C.List.fold ~init:[] ~f:(fun acc (b, _) ->
        let+ bs = step t b in
        bs @ acc)

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
    let dict = Func.dict t.fn in
    let dict = if not t.frame then dict
      else Dict.set dict Pseudo.Func.Tag.needs_stack_frame () in
    C.lift_err @@ Pseudo.Func.create ()
      ~name:(Func.name t.fn)
      ~slots:(Func.slots t.fn |> Seq.to_list)
      ~dict ~blks ~rets
end
