module type Basic = sig
  type op
  type var
  type insn
  type unop
  type binop
  type memty
  type 'a context

  (** [insn d ?dict] returns a data instruction [d] with a fresh label. *)
  val insn : ?dict:Dict.t -> op -> insn context

  (** [binop b l r ?dict] constructs a [`bop] instruction with a fresh
      label and variable containing the destination. *)
  val binop :
    ?dict:Dict.t ->
    binop ->
    Virtual.operand ->
    Virtual.operand ->
    (var * insn) context

  (** [unop o a ?dict] constructs a [`uop] instruction with a fresh label
      and variable containing the destination. *)
  val unop :
    ?dict:Dict.t ->
    unop ->
    Virtual.operand ->
    (var * insn) context

  (** [sel t c y n ?dict] constructs a [`sel] instruction with a fresh
      label and variable containing the destination. *)
  val sel :
    ?dict:Dict.t ->
    Type.basic ->
    var ->
    Virtual.operand ->
    Virtual.operand ->
    (var * insn) context

  (** [load t a ?dict] constructs a [`load] instruction with a fresh label
      and variable containing the destination. *)
  val load :
    ?dict:Dict.t ->
    memty ->
    Virtual.operand ->
    (var * insn) context

  (** [store t v a ?dict] constructs a [`store] instruction with a fresh label. *)
  val store :
    ?dict:Dict.t ->
    memty ->
    Virtual.operand ->
    Virtual.operand ->
    insn context

  (** [blit ~src ~dst word size] copies [size] bytes from the address
      in [src] to the address in [dst] in a series of loads and stores,
      where [word] is the size of a pointer.

      It is assumed that either [src] and [dst] do not overlap, or that
      they point to the same address (i.e. they overlap perfectly).

      If [size < 0], then the blit is done backwards in memory.
  *)
  val blit : src:var -> dst:var -> Type.imm_base -> int -> insn list context

  (** [ldm word src size] performs the minimum number of loads from [src]
      to cover [size] bytes, where [word] is the size of a pointer.

      If [size < 0], then the loads are done backwards in memory.

      It is identical to [blit ~src ~dst:src size], except no stores to
      [dst] are performed.
  *)
  val ldm : Type.imm_base -> var -> int -> insn list context
end

module type S = sig
  type var
  type label
  type 'a context

  include Basic
    with type op := Virtual.Insn.op
     and type var := var
     and type insn := Virtual.insn
     and type unop := Virtual.Insn.unop
     and type binop := Virtual.Insn.binop
     and type memty := Type.arg
     and type 'a context := 'a context

  (** [call0 f args vargs ?dict] constructs a void [`call] instruction
      with a fresh label. *)
  val call0 :
    ?dict:Dict.t ->
    Virtual.global ->
    Virtual.operand list ->
    Virtual.operand list ->
    Virtual.insn context

  (** [call t f args vargs ?dict] constructs a [`call] instruction with a
      fresh label and variable containing the destination. *)
  val call :
    ?dict:Dict.t ->
    Type.ret ->
    Virtual.global ->
    Virtual.operand list ->
    Virtual.operand list ->
    (var * Virtual.insn) context 

  (** [vaarg t a ?dict] constructs a [`vaarg] instruction with a fresh label
      and variable containing the destination. *)
  val vaarg :
    ?dict:Dict.t ->
    Type.arg ->
    Virtual.Insn.alist ->
    (var * Virtual.insn) context 

  (** [vastart a ?dict] constructs a [`vastart] instruction with a fresh label. *)
  val vastart :
    ?dict:Dict.t ->
    Virtual.Insn.alist ->
    Virtual.insn context 

  (** [blk ?dict ?args ?insns ~ctrl ()] returns a block with [dict],
      [args], [insns], and [ctrl], while generating a fresh label for
      the block. *)
  val blk :
    ?dict:Dict.t ->
    ?args:var list ->
    ?insns:Virtual.insn list ->
    ctrl:Virtual.ctrl ->
    unit ->
    Virtual.blk context

  (** Same as [blk], but also generates fresh labels for the [insns].
      Allows a pre-existing label for the block. *)
  val blk' :
    ?dict:Dict.t ->
    ?label:label option ->
    ?args:var list ->
    ?insns:Virtual.Insn.op list ->
    ctrl:Virtual.ctrl ->
    unit ->
    Virtual.blk context

  module Module : sig
    (** Same as [Virtual.Module.map_funs], but [f] is a context
        computation. *)
    val map_funs :
      Virtual.module_ ->
      f:(Virtual.func -> Virtual.func context) ->
      Virtual.module_ context

    (** Same as [map_funs], but for ABI-lowered modules. *)
    val map_funs_abi :
      Virtual.Abi.module_ ->
      f:(Virtual.Abi.func -> Virtual.Abi.func context) ->
      Virtual.Abi.module_ context
  end

  (** Same as the above helpers, but for the ABI variant of Virtual IR. *)
  module Abi : sig
    include Basic
      with type op := Virtual.Abi.Insn.op
       and type var := var
       and type insn := Virtual.Abi.insn
       and type unop := Virtual.Abi.Insn.unop
       and type binop := Virtual.Abi.Insn.binop
       and type memty := Type.basic
       and type 'a context := 'a context

    (** [call rets f args ?dict] constructs a [`call] instruction with a
        fresh label and a list of variables containing the destinations,
        according to [rets]. *)
    val call :
      ?dict:Dict.t ->
      (Type.basic * string) list ->
      Virtual.global ->
      Virtual.Abi.Insn.callarg list ->
      ((var * Type.basic * string) list * Virtual.Abi.insn) context

    (** [loadreg ?dict t r] fetches register [r] with type [t]. *)
    val loadreg :
      ?dict:Dict.t ->
      Type.basic ->
      string ->
      (var * Virtual.Abi.insn) context

    (** [storereg ?dict v a] stores register [r] at address [a]. *)
    val storereg :
      ?dict:Dict.t ->
      string ->
      Virtual.operand ->
      Virtual.Abi.insn context

    (** [setreg ?dict v a] loads register [r] with value [a]. *)
    val setreg :
      ?dict:Dict.t ->
      string ->
      Virtual.operand ->
      Virtual.Abi.insn context

    (** [stkargs ?dict ()] gets the beginning of the stack arguments region. *)
    val stkargs : ?dict:Dict.t -> unit -> (var * Virtual.Abi.insn) context
  end
end
