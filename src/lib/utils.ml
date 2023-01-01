module Float32 = struct
  external of_float : float -> float =
    "cgen_float_to_single_precision"

  external to_int32_ieee : float -> int32 =
    "cgen_int32_ieee_of_single_precision"

  external to_string : float -> string =
    "cgen_string_of_single_precision"
end
