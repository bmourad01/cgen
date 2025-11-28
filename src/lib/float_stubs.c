#include <caml/alloc.h>
#include <caml/custom.h>
#include <caml/hash.h>
#include <caml/memory.h>
#include <caml/mlvalues.h>
#include <caml/version.h>

#include <float.h>
#include <math.h>

#define MAX_FLOAT_DIGITS 24

#define Float_val(v) (*(float *)(Data_custom_val(v)))

intnat cgen_float32_compare_unboxed(float f, float g) {
  return (intnat)(f > g) - (intnat)(f < g) + (intnat)(f == f) -
         (intnat)(g == g);
}

int cgen_float32_compare_to_untagged(value f, value g) {
  return cgen_float32_compare_unboxed(Float_val(f), Float_val(g));
}

value cgen_float32_compare(value f, value g) {
  return Val_int(cgen_float32_compare_to_untagged(f, g));
}

/* See:

   - ocaml/runtime/hash.c
   - ocaml/stdlib/float.ml
*/
value cgen_float32_hash(value x) {
  uint32_t h = caml_hash_mix_float(0, Float_val(x));
  h ^= h >> 16;
  h *= 0x85ebca6b;
  h ^= h >> 13;
  h *= 0xc2b2ae35;
  h ^= h >> 16;
  return Val_int(h & 0x3fffffffu);
}

static struct custom_operations cgen_float32_custom_ops = {
    .identifier = (char *)"cgen_float32_custom_ops",
    .finalize = custom_finalize_default,
    .compare = cgen_float32_compare_to_untagged,
    .hash = cgen_float32_hash,
    .serialize = custom_serialize_default,
    .deserialize = custom_deserialize_default,
    .compare_ext = custom_compare_ext_default,
#if OCAML_VERSION_MAJOR >= 4 && OCAML_VERSION_MINOR >= 8
    .fixed_length = NULL,
#endif
};

#define Alloc_float()                                                          \
  caml_alloc_custom(&cgen_float32_custom_ops, sizeof(float), 0, 1)

value cgen_float32_of_float(value x) {
  CAMLparam1(x);
  CAMLlocal1(f);
  f = Alloc_float();
  Float_val(f) = (float)Double_val(x);
  CAMLreturn(f);
}

value cgen_float_of_float32(value x) { return caml_copy_double(Float_val(x)); }
value cgen_float32_is_zero(value x) { return Val_bool(Float_val(x) == 0.0f); }
value cgen_float32_is_inf(value x) { return Val_bool(isinf(Float_val(x))); }

value cgen_float32_is_negative(value x) {
  return Val_bool(signbit(Float_val(x)));
}

value cgen_float32_is_nan(value x) { return Val_bool(isnan(Float_val(x))); }

value cgen_float32_is_unordered(value x, value y) {
  return Val_bool(isunordered(Float_val(x), Float_val(y)));
}

value cgen_float32_add(value x, value y) {
  CAMLparam2(x, y);
  CAMLlocal1(f);
  f = Alloc_float();
  Float_val(f) = Float_val(x) + Float_val(y);
  CAMLreturn(f);
}

value cgen_float32_div(value x, value y) {
  CAMLparam2(x, y);
  CAMLlocal1(f);
  f = Alloc_float();
  Float_val(f) = Float_val(x) / Float_val(y);
  CAMLreturn(f);
}

value cgen_float32_mul(value x, value y) {
  CAMLparam2(x, y);
  CAMLlocal1(f);
  f = Alloc_float();
  Float_val(f) = Float_val(x) * Float_val(y);
  CAMLreturn(f);
}

value cgen_float32_neg(value x) {
  CAMLparam1(x);
  CAMLlocal1(f);
  f = Alloc_float();
  Float_val(f) = -Float_val(x);
  CAMLreturn(f);
}

value cgen_float32_sub(value x, value y) {
  CAMLparam2(x, y);
  CAMLlocal1(f);
  f = Alloc_float();
  Float_val(f) = Float_val(x) - Float_val(y);
  CAMLreturn(f);
}

value cgen_bits_of_float32(value x) {
  CAMLparam1(x);
  CAMLlocal1(i);
  float f = Float_val(x);
  i = caml_copy_int32(*(uint32_t *)&f);
  CAMLreturn(i);
}

value cgen_float32_of_bits(value x) {
  CAMLparam1(x);
  CAMLlocal1(f);
  uint32_t i = Int32_val(x);
  f = Alloc_float();
  Float_val(f) = *(float *)&i;
  CAMLreturn(f);
}

value cgen_int8_of_float32(value x) { return Val_int((int8_t)Float_val(x)); }
value cgen_int16_of_float32(value x) { return Val_int((int16_t)Float_val(x)); }

value cgen_int32_of_float32(value x) {
  return caml_copy_int32((int32_t)Float_val(x));
}

value cgen_int64_of_float32(value x) {
  return caml_copy_int64((int64_t)Float_val(x));
}

value cgen_uint8_of_float32(value x) { return Val_int((uint8_t)Float_val(x)); }

value cgen_uint16_of_float32(value x) {
  return Val_int((uint16_t)Float_val(x));
}

value cgen_uint32_of_float32(value x) {
  return caml_copy_int32((uint32_t)Float_val(x));
}

value cgen_uint64_of_float32(value x) {
  return caml_copy_int64((uint64_t)Float_val(x));
}

value cgen_float32_of_int8(value x) {
  CAMLparam1(x);
  CAMLlocal1(f);
  f = Alloc_float();
  Float_val(f) = (float)((int8_t)Int_val(x));
  CAMLreturn(f);
}

value cgen_float32_of_int16(value x) {
  CAMLparam1(x);
  CAMLlocal1(f);
  f = Alloc_float();
  Float_val(f) = (float)((int16_t)Int_val(x));
  CAMLreturn(f);
}

value cgen_float32_of_int32(value x) {
  CAMLparam1(x);
  CAMLlocal1(f);
  f = Alloc_float();
  Float_val(f) = (float)((int32_t)Int32_val(x));
  CAMLreturn(f);
}

value cgen_float32_of_int64(value x) {
  CAMLparam1(x);
  CAMLlocal1(f);
  f = Alloc_float();
  Float_val(f) = (float)((int64_t)Int64_val(x));
  CAMLreturn(f);
}

value cgen_float32_of_uint8(value x) {
  CAMLparam1(x);
  CAMLlocal1(f);
  f = Alloc_float();
  Float_val(f) = (float)((uint8_t)Int_val(x));
  CAMLreturn(f);
}

value cgen_float32_of_uint16(value x) {
  CAMLparam1(x);
  CAMLlocal1(f);
  f = Alloc_float();
  Float_val(f) = (float)((uint16_t)Int_val(x));
  CAMLreturn(f);
}

value cgen_float32_of_uint32(value x) {
  CAMLparam1(x);
  CAMLlocal1(f);
  f = Alloc_float();
  Float_val(f) = (float)((uint32_t)Int32_val(x));
  CAMLreturn(f);
}

value cgen_float32_of_uint64(value x) {
  CAMLparam1(x);
  CAMLlocal1(f);
  f = Alloc_float();
  Float_val(f) = (float)((uint64_t)Int64_val(x));
  CAMLreturn(f);
}

value cgen_string_of_float32(value x) {
  CAMLparam1(x);
  CAMLlocal1(s);
  char buf[MAX_FLOAT_DIGITS] = {0};
  snprintf(buf, sizeof(buf), "%g", Float_val(x));
  s = caml_copy_string(buf);
  CAMLreturn(s);
}

value cgen_float32_equal(value x, value y) {
  return Val_bool(Float_val(x) == Float_val(y));
}

value cgen_float32_ge(value x, value y) {
  return Val_bool(Float_val(x) >= Float_val(y));
}

value cgen_float32_gt(value x, value y) {
  return Val_bool(Float_val(x) > Float_val(y));
}

value cgen_float32_le(value x, value y) {
  return Val_bool(Float_val(x) <= Float_val(y));
}

value cgen_float32_lt(value x, value y) {
  return Val_bool(Float_val(x) < Float_val(y));
}

value cgen_bits_of_float(value x) {
  CAMLparam1(x);
  CAMLlocal1(d);
  double f = Double_val(x);
  d = caml_copy_int64(*(uint64_t *)&f);
  CAMLreturn(d);
}

value cgen_float_of_bits(value x) {
  CAMLparam1(x);
  CAMLlocal1(f);
  uint64_t i = Int64_val(x);
  f = caml_copy_double(*(double *)&i);
  CAMLreturn(f);
}

value cgen_int8_of_float(value x) { return Val_int((int8_t)Double_val(x)); }
value cgen_int16_of_float(value x) { return Val_int((int16_t)Double_val(x)); }

value cgen_int32_of_float(value x) {
  return caml_copy_int32((int32_t)Double_val(x));
}

value cgen_int64_of_float(value x) {
  return caml_copy_int64((int64_t)Double_val(x));
}

value cgen_uint8_of_float(value x) { return Val_int((uint8_t)Double_val(x)); }
value cgen_uint16_of_float(value x) { return Val_int((uint16_t)Double_val(x)); }

value cgen_uint32_of_float(value x) {
  return caml_copy_int32((uint32_t)Double_val(x));
}

value cgen_uint64_of_float(value x) {
  return caml_copy_int64((uint64_t)Double_val(x));
}

value cgen_float_of_int8(value x) {
  CAMLparam1(x);
  CAMLlocal1(f);
  f = caml_copy_double((double)((int8_t)Int_val(x)));
  CAMLreturn(f);
}

value cgen_float_of_int16(value x) {
  CAMLparam1(x);
  CAMLlocal1(f);
  f = caml_copy_double((double)((int16_t)Int_val(x)));
  CAMLreturn(f);
}

value cgen_float_of_int32(value x) {
  CAMLparam1(x);
  CAMLlocal1(f);
  f = caml_copy_double((double)((int32_t)Int32_val(x)));
  CAMLreturn(f);
}

value cgen_float_of_int64(value x) {
  CAMLparam1(x);
  CAMLlocal1(f);
  f = caml_copy_double((double)((int64_t)Int64_val(x)));
  CAMLreturn(f);
}

value cgen_float_of_uint8(value x) {
  CAMLparam1(x);
  CAMLlocal1(f);
  f = caml_copy_double((double)((uint8_t)Int_val(x)));
  CAMLreturn(f);
}

value cgen_float_of_uint16(value x) {
  CAMLparam1(x);
  CAMLlocal1(f);
  f = caml_copy_double((double)((uint16_t)Int_val(x)));
  CAMLreturn(f);
}

value cgen_float_of_uint32(value x) {
  CAMLparam1(x);
  CAMLlocal1(f);
  f = caml_copy_double((double)((uint32_t)Int32_val(x)));
  CAMLreturn(f);
}

value cgen_float_of_uint64(value x) {
  CAMLparam1(x);
  CAMLlocal1(f);
  f = caml_copy_double((double)((uint64_t)Int64_val(x)));
  CAMLreturn(f);
}

value cgen_float_is_unordered(value x, value y) {
  return Val_bool(isunordered(Double_val(x), Double_val(y)));
}

value cgen_float_is_ordered(value x, value y) {
  return Val_bool(!isunordered(Double_val(x), Double_val(y)));
}
