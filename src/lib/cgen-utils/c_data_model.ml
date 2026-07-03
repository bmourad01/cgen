open Core

type model =
  | LP32
  | ILP32
  | LP64
  | LLP64
  | ILP64
[@@deriving bin_io, compare, equal, hash, sexp]

type t = {
  model         : model;
  char_signed   : bool;
  va_list_size  : int;
  va_list_align : int;
} [@@deriving bin_io, compare, equal, hash, sexp]

let create ~model ~char_signed ~va_list_size ~va_list_align =
  if va_list_size <= 0 then
    failwithf "create: invalid va_list_size %d (must be positive)" va_list_size ();
  if va_list_align <= 0 then
    failwithf "create: invalid va_list_align %d (must be positive)" va_list_align ();
  if (va_list_align land (va_list_align - 1)) <> 0 then
    failwithf "create: va_list_align must be a power of 2 (got %d)" va_list_align ();
  {model; char_signed; va_list_size; va_list_align}

let model t = t.model
let char_signed t = t.char_signed
let va_list_size t = t.va_list_size
let va_list_align t = t.va_list_align

let char_bits = 8
let bool_bits = 8
let short_bits = 16
let long_long_bits = 64
let float_bits = 32
let double_bits = 64

let int_bits t = match t.model with
  | LP32 -> 16
  | ILP32 | LP64 | LLP64 -> 32
  | ILP64 -> 64

let long_bits t = match t.model with
  | LP32 | ILP32 | LLP64 -> 32
  | LP64 | ILP64 -> 64

let pointer_bits t = match t.model with
  | LP32 | ILP32 -> 32
  | LP64 | LLP64 | ILP64 -> 64

let char_bytes = char_bits / 8
let bool_bytes = bool_bits / 8
let short_bytes = short_bits / 8
let long_long_bytes = long_long_bits / 8
let float_bytes = float_bits / 8
let double_bytes = double_bits / 8
let int_bytes t = int_bits t / 8
let long_bytes t = long_bits t / 8
let pointer_bytes t = pointer_bits t / 8
