(** A generic, target-independent peephole engine over Pseudo IR.

    The engine fuses what would otherwise be one full-function traversal per
    rewrite rule into a single left-to-right scan of each block, trying a
    priority-ordered list of rules at every instruction. A rewrite made by an
    earlier rule is visible to a later rule at a subsequent position within the
    same scan, so simple rewrites cascade without waiting for another round.

    Only window-local rules belong here. CFG-structural transformations (block
    merging, jump threading, branch inversion) operate across blocks and are
    driven separately by the caller.
*)

module Take : sig
  (** A fixed-size window of instructions taken from a block, with its arity
      carried in a phantom index.

      The elements are stored inline in the single constructor block; [T0] is
      the "fewer than requested were available" case and, being universal in
      the index, inhabits every arity, so {!View.take} needs no [option] wrapper.
  *)
  type ('a, _) t =
    | T0 : ('a, _) t
    | T1 : 'a -> ('a, [`one]) t
    | T2 : 'a * 'a -> ('a, [`two]) t
    | T3 : 'a * 'a * 'a -> ('a, [`three]) t

  (** A key selecting how many instructions to take; its phantom index fixes the
      arity of the resulting {!taken}. *)
  type _ key =
    | K1 : [`one] key
    | K2 : [`two] key
    | K3 : [`three] key
end

(** A read-only, random-access view of a block's instruction payloads, handed
    to each rule. *)
module View : sig
  type 'a t

  (** The number of instruction slots in the block (including any that earlier
      edits in this scan have marked for deletion). *)
  val length : 'a t -> int

  (** [get_exn v i] is the payload at index [i]. It reflects rewrites already
      applied earlier in the same scan.

      Raises [Invalid_argument] if [i] is out of bounds.
  *)
  val get_exn : 'a t -> int -> 'a

  (** [take v i k] is the [k]-arity window of consecutive payloads starting at
      index [i], or [T0] if the block has fewer than [k] instructions left.
      Allocates only the single window block on success (nothing on [T0]). *)
  val take : 'a t -> int -> 'k Take.key -> ('a, 'k) Take.t
end

type 'a view = 'a View.t

(** An edit addresses an absolute index into the block. *)
module Edit : sig
  type 'a t =
    | Rewrite of int * 'a
    (** [Rewrite (i, x)] replaces the payload at index [i], keeping its label. *)
    | Delete of int
    (** [Delete i] drops the instruction at index [i]. *)
end

type 'a edit = 'a Edit.t

(** A rule inspects a block's instructions and a cursor position.

    On a match, it returns the edits to apply and the index at which scanning
    resumes (which must be strictly greater than the matched position). Returning
    [None] means no match was found at this position.

    A rule matching at position [p] and resuming at [next] may only [Delete]
    indices in the half-open window [\[p, next)] (its own consumed window).
    Deleted indices are thus always behind the advancing cursor, and since no
    rule reads behind the cursor, a deleted instruction is never observed by a
    later rule. [Rewrite]s ahead of [next] are permitted and are re-examined
    when the cursor reaches them.
*)
type 'a rule = 'a view -> int -> ('a edit list * int) option

(** [run ~changed ~rules fn] applies [rules] to every block of [fn], each block
    scanned left to right applying the first matching rule at each position, and
    rescanned to a local fixpoint so a rewrite that opens a window behind the
    cursor is caught without another whole-function round.

    [changed] is set to [true] if any instruction was rewritten or dropped. The
    caller still drives convergence across blocks (e.g. after block merging) by
    re-running as needed.
*)
val run :
  changed:bool ref ->
  rules:'i rule list ->
  ('i, 'r) Pseudo.func ->
  ('i, 'r) Pseudo.func
