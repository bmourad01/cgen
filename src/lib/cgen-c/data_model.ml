open Core

include Cgen_utils.C_data_model

let size_t t = match model t with
  | LP32 | LP64 | ILP64 -> Type.long_ ~sign:Type.Sunsigned ()
  | ILP32 -> Type.int_ ~sign:Type.Sunsigned ()
  | LLP64 -> Type.longlong_ ~sign:Type.Sunsigned ()

let ptrdiff_t t = match model t with
  | LP32 | LP64 | ILP64 -> Type.long_ ()
  | ILP32 -> Type.int_ ()
  | LLP64 -> Type.longlong_ ()

(* The compiler builtin type `__builtin_va_list`, whose size and alignment
   the target declares in the data model (it is ABI-specific, not derivable
   from the integer model).

   We realize it as an array of `count` elements, each `va_list_align` bytes
   wide, so its layout matches the declared size and alignment. The backend
   writes the actual fields during `vastart`.
*)
let va_list t : Texpr.ty =
  let size = va_list_size t and align = va_list_align t in
  let elem =
    if align = char_bytes then Type.char_ Type.Ssigned
    else if align = short_bytes then Type.short_ ()
    else if align = int_bytes t then Type.int_ ()
    else if align = long_bytes t then Type.long_ ()
    else if align = long_long_bytes then Type.longlong_ ()
    else failwithf "va_list: no %d-byte integer type in this data model" align () in
  let count = size / align in
  let sz = Texpr.int_ (Cgen.Bv.M64.int count) ~ty:(size_t t) in
  Type.array ~size:sz elem
