open Core

type t [@@deriving bin_io]

external of_float : float -> t = "cgen_float32_of_float"
external to_float : t -> float = "cgen_float_of_float32"

external is_zero     : t -> bool = "cgen_float32_is_zero" [@@noalloc]
external is_inf      : t -> bool = "cgen_float32_is_inf" [@@noalloc]
external is_negative : t -> bool = "cgen_float32_is_negative" [@@noalloc]
external is_nan      : t -> bool = "cgen_float32_is_nan" [@@noalloc]
external is_unordered : t -> t -> bool = "cgen_float32_is_unordered" [@@noalloc]

let is_ordered x y = not @@ is_unordered x y

external add : t -> t -> t = "cgen_float32_add"
external div : t -> t -> t = "cgen_float32_div"
external mul : t -> t -> t = "cgen_float32_mul"
external neg : t -> t      = "cgen_float32_neg"
external rem : t -> t -> t = "cgen_float32_rem"
external sub : t -> t -> t = "cgen_float32_sub"

let (+)   x y = add x y
let (/)   x y = div x y
let ( * ) x y = mul x y
let (-~)  x   = neg x
let ( % ) x   = rem x
let (-)   x y = sub x y

external bits    : t -> int32 = "cgen_bits_of_float32"
external of_bits : int32 -> t = "cgen_float32_of_bits"

external to_int8   : t     -> int   = "cgen_int8_of_float32" [@@noalloc]
external to_int16  : t     -> int   = "cgen_int16_of_float32" [@@noalloc]
external to_int32  : t     -> int32 = "cgen_int32_of_float32"
external to_int64  : t     -> int64 = "cgen_int64_of_float32"
external to_uint8  : t     -> int   = "cgen_uint8_of_float32" [@@noalloc]
external to_uint16 : t     -> int   = "cgen_uint16_of_float32" [@@noalloc]
external to_uint32 : t     -> int32 = "cgen_uint32_of_float32"
external to_uint64 : t     -> int64 = "cgen_uint64_of_float32"
external of_int8   : int   -> t     = "cgen_float32_of_int8"
external of_int16  : int   -> t     = "cgen_float32_of_int16"
external of_int32  : int32 -> t     = "cgen_float32_of_int32"
external of_int64  : int64 -> t     = "cgen_float32_of_int64"
external of_uint8  : int   -> t     = "cgen_float32_of_uint8"
external of_uint16 : int   -> t     = "cgen_float32_of_uint16"
external of_uint32 : int32 -> t     = "cgen_float32_of_uint32"
external of_uint64 : int64 -> t     = "cgen_float32_of_uint64"

external to_string : t -> string = "cgen_string_of_float32"

let of_string s = of_float @@ Float.of_string s

external equal : t -> t -> bool = "cgen_float32_equal" [@@noalloc]

let (=) x y = equal x y
let (<>) x y = not (x = y)

external (>=) : t -> t -> bool = "cgen_float32_ge" [@@noalloc]
external (>)  : t -> t -> bool = "cgen_float32_gt" [@@noalloc]
external (<=) : t -> t -> bool = "cgen_float32_le" [@@noalloc]
external (<)  : t -> t -> bool = "cgen_float32_lt" [@@noalloc]

external compare : t -> t -> int = "cgen_float32_compare" [@@noalloc]

let sexp_of_t x = Sexp.Atom (to_string x)

external hash : t -> int = "cgen_float32_hash" [@@noalloc]

let t_of_sexp = function
  | Sexp.Atom s -> of_string s
  | x ->
    let exn = Failure "Float32.t_of_sexp: atom needed" in
    raise @@ Sexplib.Conv.Of_sexp_error (exn, x)

include Hashable.Make_plain_and_derive_hash_fold_t(struct
    type nonrec t = t
    let sexp_of_t = sexp_of_t
    let compare = compare
    let hash = hash
  end)
