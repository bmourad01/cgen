(** C data models.

    A data model fixes the widths of the integer and pointer types
    whose sizes are implementation-defined in the C standard, together
    with the signedness of plain [char]. It is a property of the target
    platform / ABI; backend targets declare their data model.

    The widths of [_Bool], [short], [long long], [float], and [double]
    are fixed across all the models supported here.

    The C-type-valued helpers ([size_t], [ptrdiff_t]) live in the C
    frontend's own [Data_model], which extends this module, since they
    construct C types.
*)

(** Known data models.

    {v
    | Model | int | long | pointer |
    |-------|-----|------|---------|
    | LP32  |  16 |   32 |      32 |
    | ILP32 |  32 |   32 |      32 |
    | LP64  |  32 |   64 |      64 |
    | LLP64 |  32 |   32 |      64 |
    | ILP64 |  64 |   64 |      64 |
    v}

    Widths are in bits.
*)
type model =
  | LP32
  | ILP32
  | LP64
  | LLP64
  | ILP64
[@@deriving bin_io, compare, equal, hash, sexp]

(** A data model description *)
type t [@@deriving bin_io, compare, equal, hash, sexp]

(** [create ~model ~char_signed ~va_list_size ~va_list_align] builds a
    data model description.

    [char_signed] determines whether a plain [char] is signed or not,
    since C99 §6.2.5 leaves this as an implementation-defined detail.

    [va_list_size] and [va_list_align] are the size and alignment
    in bytes of the target's [__builtin_va_list] object. These are
    ABI-specific (not derivable from the integer model), so the
    target declares them.
*)
val create :
  model:model ->
  char_signed:bool ->
  va_list_size:int ->
  va_list_align:int ->
  t

(** The underlying model. *)
val model : t -> model

(** Whether plain [char] is signed under this description. *)
val char_signed : t -> bool

(** Size in bytes of the [__builtin_va_list] object. *)
val va_list_size : t -> int

(** Alignment in bytes of the [__builtin_va_list] object. *)
val va_list_align : t -> int

(** Width of [char] in bits. *)
val char_bits : int

(** Width of [_Bool] in bits. *)
val bool_bits : int

(** Width of [short] in bits. *)
val short_bits : int

(** Width of [long long] in bits. *)
val long_long_bits : int

(** Width of [float] in bits. *)
val float_bits : int

(** Width of [double] in bits. *)
val double_bits : int

(** Width of [int] in bits under the given description. *)
val int_bits : t -> int

(** Width of [long] in bits under the given description. *)
val long_bits : t -> int

(** Width of a pointer in bits under the given description. *)
val pointer_bits : t -> int

(** Size of [char] in bytes. *)
val char_bytes : int

(** Size of [_Bool] in bytes. *)
val bool_bytes : int

(** Size of [short] in bytes. *)
val short_bytes : int

(** Size of [long long] in bytes. *)
val long_long_bytes : int

(** Size of [float] in bytes. *)
val float_bytes : int

(** Size of [double] in bytes. *)
val double_bytes : int

(** Size of [int] in bytes under the given description. *)
val int_bytes : t -> int

(** Size of [long] in bytes under the given description. *)
val long_bytes : t -> int

(** Size of a pointer in bytes under the given description. *)
val pointer_bytes : t -> int
