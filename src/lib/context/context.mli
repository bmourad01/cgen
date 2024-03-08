(** The compilation context.

    All elements of the compilation pipeline are expected to be
    parameterized by this context. It contains various book keeping
    and state.
*)

open Core
open Monads.Std
open Regular.Std

(** The state for the compilation context. *)
module State : sig
  type t

  include Regular.S with type t := t
end

type state = State.t

(** The compilation context. *)
type 'a t

(** Terminates the computation with an error. *)
val fail : Error.t -> 'a t

(** Same as [fail], but formats a pretty-printed error message. *)
val failf : ('a, Format.formatter, unit, unit -> 'b t) format4 -> 'a

(** Lifts an [Or_error] computation into the context.

    If it is [Ok x], then [x] is returned, otherwise the computation fails
    with the error.
*)
val lift_err : 'a Or_error.t -> 'a t

(** Returns the current target descriptor. *)
val target : Target.t t

(** Local state that can be used during an analysis or transformation pass
    within the compilation context, without use of monad transformers.

    This state is not persistent between runs of compilation context.
*)
module Local : sig
  (** [set k v] sets the value associated with key [k] to [v]. *)
  val set : 'a Dict.tag -> 'a -> unit t

  (** [get k ~default] returns the value associated with [k] if it exists,
      and [default] otherwise. *)
  val get : 'a Dict.tag -> default:'a -> 'a t

  (** [erase k] removes [k] from the local state. This can be useful to
      reset the state for re-runs or to discard state that is isolated to
      a particular analysis or transformation. *)
  val erase : 'a Dict.tag -> unit t
end

(** The target-specific implementation needed for the compilation pipeline. *)
module type Machine = Machine_intf.S
  with type 'a context := 'a t

(** [register_machine t m] registers the machine implementation [m] for
    target descriptor [t].

    @raise Invalid_argument if [t] is already registered with a machine.
*)
val register_machine : Target.t -> (module Machine) -> unit

(** Returns the target machine implementation for the current context. *)
val machine : (module Machine) t

type var = Var.t

module Var : sig
  (** Generates a fresh temporary variable. *)
  val fresh : var t
end

type label = Label.t

module Label : sig
  (** Generates a fresh program label. *)
  val fresh : label t
end

(** Helpers for generating [Virtual] terms. *)
module Virtual : sig
  (** [insn d ?dict] returns a data instruction [d] with a fresh label. *)
  val insn : ?dict:Dict.t -> Virtual.Insn.op -> Virtual.insn t

  (** [binop b l r ?dict] constructs a [`bop] instruction with a fresh
      label and variable containing the destination. *)
  val binop :
    ?dict:Dict.t ->
    Virtual.Insn.binop ->
    Virtual.operand ->
    Virtual.operand ->
    (var * Virtual.insn) t

  (** [unop o a ?dict] constructs a [`uop] instruction with a fresh label
      and variable containing the destination. *)
  val unop :
    ?dict:Dict.t ->
    Virtual.Insn.unop ->
    Virtual.operand ->
    (var * Virtual.insn) t 

  (** [sel t c y n ?dict] constructs a [`sel] instruction with a fresh
      label and variable containing the destination. *)
  val sel :
    ?dict:Dict.t ->
    Type.basic ->
    var ->
    Virtual.operand ->
    Virtual.operand ->
    (var * Virtual.insn) t

  (** [call0 f args vargs ?dict] constructs a void [`call] instruction
      with a fresh label. *)
  val call0 :
    ?dict:Dict.t ->
    Virtual.global ->
    Virtual.operand list ->
    Virtual.operand list ->
    Virtual.insn t

  (** [call t f args vargs ?dict] constructs a [`call] instruction with a
      fresh label and variable containing the destination. *)
  val call :
    ?dict:Dict.t ->
    Type.ret ->
    Virtual.global ->
    Virtual.operand list ->
    Virtual.operand list ->
    (var * Virtual.insn) t 

  (** [load t a ?dict] constructs a [`load] instruction with a fresh label
      and variable containing the destination. *)
  val load :
    ?dict:Dict.t ->
    Type.basic ->
    Virtual.operand ->
    (var * Virtual.insn) t 

  (** [store t v a ?dict] constructs a [`store] instruction with a fresh label. *)
  val store :
    ?dict:Dict.t ->
    Type.basic ->
    Virtual.operand ->
    Virtual.operand ->
    Virtual.insn t 

  (** [vaarg t a ?dict] constructs a [`vaarg] instruction with a fresh label
      and variable containing the destination. *)
  val vaarg :
    ?dict:Dict.t ->
    Type.arg ->
    Virtual.Insn.alist ->
    (var * Virtual.insn) t 

  (** [vastart a ?dict] constructs a [`vastart] instruction with a fresh label. *)
  val vastart :
    ?dict:Dict.t ->
    Virtual.Insn.alist ->
    Virtual.insn t 

  (** [ref a ?dict] constructs a [`ref] instruction with a fresh label and a
      variable containing the destination. *)
  val ref : ?dict:Dict.t -> Virtual.operand -> (var * Virtual.insn) t

  (** [unref s a ?dict] constructs an [`unref] instruction for type [s] with
      a fresh label and a variable containing the destination. *)
  val unref : ?dict:Dict.t -> string -> Virtual.operand -> (var * Virtual.insn) t

  (** [blit ~src ~dst word size] copies [size] bytes from the address
      in [src] to the address in [dst] in a series of loads and stores,
      where [word] is the size of a pointer.

      It is assumed that either [src] and [dst] do not overlap, or that
      they point to the same address (i.e. they overlap perfectly).

      If [size < 0], then the blit is done backwards in memory.
  *)
  val blit : src:var -> dst:var -> Type.imm_base -> int -> Virtual.insn list t

  (** [ldm word src size] performs the minimum number of loads from [src]
      to cover [size] bytes, where [word] is the size of a pointer.

      If [size < 0], then the loads are done backwards in memory.

      It is identical to [blit ~src ~dst:src size], except no stores to
      [dst] are performed.
  *)
  val ldm : Type.imm_base -> var -> int -> Virtual.insn list t

  (** [blk ?dict ?args ?insns ~ctrl ()] returns a block with [dict],
      [args], [insns], and [ctrl], while generating a fresh label for
      the block. *)
  val blk :
    ?dict:Dict.t ->
    ?args:var list ->
    ?insns:Virtual.insn list ->
    ctrl:Virtual.ctrl ->
    unit ->
    Virtual.blk t

  (** Same as [blk], but also generates fresh labels for the [insns].
      Allows a pre-existing label for the block. *)
  val blk' :
    ?dict:Dict.t ->
    ?label:label option ->
    ?args:var list ->
    ?insns:Virtual.Insn.op list ->
    ctrl:Virtual.ctrl ->
    unit ->
    Virtual.blk t

  module Module : sig
    (** Same as [Virtual.Module.map_funs], but [f] is a context
        computation. *)
    val map_funs :
      Virtual.module_ ->
      f:(Virtual.func -> Virtual.func t) ->
      Virtual.module_ t
  end

  (** Same as the above helpers, but for the ABI variant of Virtual IR. *)
  module Abi : sig
    val insn : ?dict:Dict.t -> Virtual.Abi.Insn.op -> Virtual.Abi.insn t

    val binop :
      ?dict:Dict.t ->
      Virtual.Abi.Insn.binop ->
      Virtual.Abi.operand ->
      Virtual.Abi.operand ->
      (var * Virtual.Abi.insn) t

    val unop :
      ?dict:Dict.t ->
      Virtual.Abi.Insn.unop ->
      Virtual.Abi.operand ->
      (var * Virtual.Abi.insn) t

    val sel :
      ?dict:Dict.t ->
      Type.basic ->
      Virtual.Abi.var ->
      Virtual.Abi.operand ->
      Virtual.Abi.operand ->
      (var * Virtual.Abi.insn) t

    val call :
      ?dict:Dict.t ->
      string list ->
      Virtual.Abi.global ->
      Virtual.Abi.operand list ->
      Virtual.Abi.insn t

    val load :
      ?dict:Dict.t ->
      Type.basic ->
      Virtual.Abi.operand ->
      (var * Virtual.Abi.insn) t

    val store :
      ?dict:Dict.t ->
      Type.basic ->
      Virtual.Abi.operand ->
      Virtual.Abi.operand ->
      Virtual.Abi.insn t

    (** [storev ?dict v a] stores vector register [v] at address [a]. *)
    val storev :
      ?dict:Dict.t ->
      string ->
      Virtual.Abi.operand ->
      Virtual.Abi.insn t

    (** [stkargs ?dict ()] gets the beginning of the stack arguments region. *)
    val stkargs : ?dict:Dict.t -> unit -> (var * Virtual.Abi.insn) t

    val blit :
      src:Virtual.Abi.var ->
      dst:Virtual.Abi.var ->
      Type.imm_base ->
      int ->
      Virtual.Abi.insn list t

    val ldm :
      Type.imm_base ->
      Virtual.Abi.var ->
      int ->
      Virtual.Abi.insn list t
  end
end

(** Initializes the state. *)
val init : Target.t -> state

(** [run x s] runs the computation [x] with the initial state [s],
    and returns the result of computing [x] with the updated state,
    or an error if the computation failed. *)
val run : 'a t -> state -> ('a * state) Or_error.t

(** [eval x s] is the same as [run x s], except the updated state is
    discarded when [x] terminates. *)
val eval : 'a t -> state -> 'a Or_error.t

module Syntax : sig
  include Monad.Syntax.S with type 'a t := 'a t
  include Monad.Syntax.Let.S with type 'a t := 'a t

  (** Attempts to unwrap an [Or_error] computation into the context, and
      fails if it is an error. *)
  val (>>?) : 'a Or_error.t -> ('a -> 'b t) -> 'b t

  (** Same as the [(>>?)] infix notation. *)
  val (let*?) : 'a Or_error.t -> ('a -> 'b t) -> 'b t
end

include Monad.S with type 'a t := 'a t and module Syntax := Syntax
