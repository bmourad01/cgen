(** C data models.

    The model proper is {!Cgen_utils.C_data_model} (so backend targets can
    declare it); this module re-exports it and adds the C-type-valued
    standard-library typedefs.
*)

include module type of struct
  include Cgen_utils.C_data_model
end

(** {1 Standard library typedefs}

    The standard integer type each implementation-defined typedef
    resolves to under this model.
*)

(** [size_t] (§7.17): the unsigned integer type of a [sizeof] result.
    Pointer-width in every supported model. *)
val size_t : t -> _ Type.t

(** [ptrdiff_t] (§7.17): the signed integer type of a pointer difference.
    Pointer-width in every supported model. *)
val ptrdiff_t : t -> _ Type.t

(** [va_list] (§7.16): the [__builtin_va_list] object type, realized as an
    array whose size and alignment match the target-declared
    [va_list_size] and [va_list_align]. *)
val va_list : t -> Texpr.ty
