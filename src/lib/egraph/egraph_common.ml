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

module Matcher = Matcher.Make(struct
    type op = Enode.op [@@deriving compare, equal, hash, sexp]
    type term = enode
    type id = Id.t [@@deriving equal]

    let is_commutative = Enode.is_commutative

    let term_op : term -> op option = function
      | N (op, _) -> Some op
      | U _ -> None

    let term_args : term -> id list = function
      | N (_, args) -> args
      | U _ -> []

    let term_union : term -> (id * id) option = function
      | U {pre; post} -> Some (pre, post)
      | N _ -> None

    let pp_id = Id.pp
    let pp_op = Enode.pp_op
  end)

module Y = Matcher.Yield
module VM = Matcher.VM

(* Allow rules to call an OCaml function that performs some action
   based on the current substitution. *)
type 'a callback = subst -> 'a

type pattern = Matcher.pat [@@deriving compare, equal, hash, sexp]

let pp_pattern = Matcher.pp_pat

(* An action to be taken when a pattern has been successfully
   matched.

   [Static p]: the term is always rewritten to [p].

   [Cond (p, k)]: the term is rewrtitten to [p] if [k] is
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

(* The compiled program for matching `pre` patterns. *)
type rules = (formula * bool) Matcher.program

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
  input          : Input.t;               (* Analyses about the function. *)
  classes        : Uf.t;                  (* The union-find for all e-classes. *)
  node           : enode Vec.t;           (* All e-nodes, indexed by ID. *)
  typs           : Type.t Uopt.t Vec.t;   (* The type of each node. *)
  memo           : (enode, id) Hashtbl.t; (* The hash-cons for optimized terms. *)
  lmoved         : Iset.t Label.Table.t;  (* Set of IDs that were moved to a given label. *)
  imoved         : Lset.t Vec.t;          (* Set of labels that were moved for a given ID. *)
  mutable pinned : Bitset.t;           (* IDs that should not be rescheduled. *)
  ilbl           : Label.t Uopt.t Vec.t;  (* Maps IDs to labels. *)
  lval           : id Label.Table.t;      (* Maps labels to IDs. *)
  depth_limit    : int;                   (* Maximum rewrite depth. *)
  match_limit    : int;                   (* Maximum rewrites per term. *)
  rules          : rules;                 (* The compiled matcher program. *)
}

type egraph = t

let compile ~name rules =
  (* XXX: the previous implementation also reversed the rule order,
     and now the testsuite relies on that behavior. Maybe the real
     fix is in changing how the extractor breaks ties. *)
  Matcher.compile ~name @@ List.rev_map rules
    ~f:(fun r -> r.pre, (r.post, r.subsume))

let find t id = Uf.find t.classes id
let node t id = Vec.get_exn t.node id
let dominates t = t.input.rdom
let const t id = Enode.const ~node:(node t) @@ node t id
let typeof t id = Vec.get_exn t.typs id |> Uopt.to_option
let labelof t id = Vec.get_exn t.ilbl id |> Uopt.to_option
let set_label t id l = Vec.set_exn t.ilbl id @@ Uopt.some l
let clear_label t id = Vec.set_exn t.ilbl id Uopt.none
let movedof t id = Vec.get_exn t.imoved id

let add_moved t id = function
  | [] -> ()
  | ls ->
    let init = Vec.get_exn t.imoved id in
    Vec.set_exn t.imoved id @@ List.fold ls ~init ~f:Lset.add

let set_pinned t id = t.pinned <- Bitset.set t.pinned id
let is_pinned t id = Bitset.mem t.pinned id

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
