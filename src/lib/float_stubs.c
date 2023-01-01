#include <caml/alloc.h>
#include <caml/mlvalues.h>
#include <float.h>
#include <stdio.h>

#define MAX_FLOAT_DIGITS 24

CAMLprim value cgen_float_to_single_precision(value d) {
  return caml_copy_double((float)Double_val(d));
}

CAMLprim value cgen_int32_ieee_of_single_precision(value d) {
  float f = (float)Double_val(d);
  uint32_t i = *(uint32_t*)&f;
  return caml_copy_int32(i);
}

CAMLprim value cgen_string_of_single_precision(value d) {
  char buf[MAX_FLOAT_DIGITS] = {0};
  float f = (float)Double_val(d);
  snprintf(buf, sizeof(buf), "%f", f);
  return caml_copy_string(buf);
}
