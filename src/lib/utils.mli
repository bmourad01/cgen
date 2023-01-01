module Float32 : sig
  (** Truncates the float to a single-precision number. *)
  val of_float : float -> float

  (** Returns the 32-bit integer representation of the single-precision
      number. *)
  val to_int32_ieee : float -> int32

  (** Returns the string representation of the single-precision number. *)
  val to_string : float -> string
end
