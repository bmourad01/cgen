open Core
open Regular.Std

module Id = Egraph_id
module Enode = Egraph_node
module Input = Egraph_input
module Uf = Egraph_uf
module Lset = Label.Tree_set
module Iset = Id.Tree_set

type id = Id.t [@@deriving bin_io, compare, equal, hash, sexp]
type enode = Enode.t
type subst = Egraph_subst.t

let empty_subst : subst = String.Map.empty

(* Allow rules to call an OCaml function that performs some action
   based on the current substitution. *)
type 'a callback = subst -> 'a

(* A pattern is either:

   [V x]: a variable [x] which represents a substitution for a
   unique term.

   [P (o, ps)]: an e-node with an operator [o] and children [ps].
*)
type pattern =
  | V of string
  | P of Enode.op * pattern list
[@@deriving compare, equal, hash, sexp]

let rec pp_pattern ppf = function
  | V x -> Format.fprintf ppf "?%s" x
  | P (o, []) -> Format.fprintf ppf "%a" Enode.pp_op o
  | P (o, ps) ->
    let pp_sep ppf () = Format.fprintf ppf " " in
    Format.fprintf ppf "(%a %a)" Enode.pp_op o
      (Format.pp_print_list ~pp_sep pp_pattern) ps

(* An action to be taken when a pattern has been successfully
   matched.

   [Static p]: the term is always rewritten to [p].

   [Cond (p, k)]: the rerm is rewrtitten to [p] if [k] is
   satisfied.

   [Dyn f]: if [f] returns [Some p], then the term is rewritten
   to [p].
*)
type formula =
  | Static of pattern
  | Cond of pattern * bool callback
  | Dyn of pattern option callback

(* A rule consists of a pattern [pre] that a node must successfully
   match with. Matching with [pre] produces a substitution, which
   is then applied to [post] to yield a rewritten term.

   [subsume] indicates that the rewritten term is already optimal
   and no further rewrites should be applied.
*)
type rule = {
  pre     : pattern;
  post    : formula;
  subsume : bool;
}

(* The children of a pattern to be matched against, and a
   post-condition, as well as a flag marking the rewritten
   term as subsuming. *)
type toplevel = pattern list * formula * bool

(* Map top-level operators to their actions. This helps to
   cut down the search space as we look to apply rules to
   a given node. *)
type rules = (Enode.op, toplevel list) Hashtbl.t

(* The actual e-graph data structure.

   Aside from the typical elements (i.e. our hash-consing of e-nodes
   and our union-find for canonicalization), we also have various
   tables that are keeping track of the relationship between an ID
   and its position (label) in the CFG representation.

   This gets a bit more complex when we want to perform optimizations
   related to code motion (e.g. LICM, CSE, hoisting, sinking), so that's
   what all the extra hash tables are for.

   See the [Egraph_sched], [Extractor_core], and [Extractor_cfg] modules
   for examples of how this information gets used.
*)
type t = {
  input       : Input.t;                (* Analyses about the function. *)
  classes     : Uf.t;                   (* The union-find for all e-classes. *)
  node        : enode Vec.t;            (* All e-nodes, indexed by ID. *)
  typs        : Type.t Uopt.t Vec.t;    (* The type of each node. *)
  memo        : (enode, id) Hashtbl.t;  (* The hash-cons for optimized terms. *)
  lmoved      : Iset.t Label.Table.t;   (* Set of IDs that were moved to a given label. *)
  imoved      : Lset.t Id.Table.t;      (* Set of labels that were moved for a given ID. *)
  idest       : Label.t Id.Table.t;     (* The label a given ID was moved to. *)
  licm        : Id.Hash_set.t;          (* IDs that were moved via LICM. *)
  isrc        : Label.t Id.Table.t;     (* Maps unmoved IDs to labels before CSE. *)
  lval        : id Label.Table.t;       (* Maps labels to IDs. *)
  depth_limit : int;                    (* Maximum rewrite depth. *)
  match_limit : int;                    (* Maximum rewrites per term. *)
  rules       : rules;                  (* The table of rewrite rules. *)
}

type egraph = t

let create_table rules =
  let t = Hashtbl.create (module struct
      type t = Enode.op [@@deriving compare, hash, sexp]
    end) in
  List.iter rules ~f:(fun r -> match r.pre with
      | P (o, ps) -> Hashtbl.add_multi t ~key:o ~data:(ps, r.post, r.subsume)
      | V x ->
        invalid_argf "Cannot create a rule with a variable \
                      %s at the top-level" x ());
  t

let find t id = Uf.find t.classes id
let node t id = Vec.get_exn t.node id
let dominates t = t.input.rdom
let const t id = Enode.const ~node:(node t) @@ node t id
let typeof t id = Vec.get_exn t.typs id |> Uopt.to_option

let typeof_var t x =
  Typecheck.Env.typeof_var t.input.fn x t.input.tenv |> Or_error.ok

let typeof_typ t n = match Typecheck.Env.typeof_typ n t.input.tenv with
  | Ok t -> Some (t :> Type.t)
  | Error _ -> None

let word t =
  (Target.word @@ Typecheck.Env.target t.input.tenv :> Type.t)

let wordsz t =
  Type.sizeof_imm_base @@
  Target.word @@
  Typecheck.Env.target t.input.tenv

let typenames t =
  Typecheck.Env.typenames t.input.tenv |>
  Seq.map ~f:(fun s -> `name s)
