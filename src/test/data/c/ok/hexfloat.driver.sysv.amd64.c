#include <assert.h>

extern double hf_frac(void);
extern double hf_no_point(void);
extern double hf_no_int(void);
extern double hf_upper(void);
extern float hf_float(void);

int
main(void) {
  assert(hf_frac() == 12.0);
  assert(hf_no_point() == 0.0625);
  assert(hf_no_int() == 1.0);
  assert(hf_upper() == 4.0);
  assert(hf_float() == 0.0625f);
  return 0;
}
