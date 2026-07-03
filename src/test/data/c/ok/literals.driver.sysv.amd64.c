#include <assert.h>

extern long hex_uint_wrap(void);
extern long dec_long_nowrap(void);
extern int hex_ull_is_unsigned(void);
extern int oct_value(void);
extern int bin_value(void);

int
main(void) {
  assert(hex_uint_wrap() == 0);
  assert(dec_long_nowrap() == 4294967296L);
  assert(hex_ull_is_unsigned() == 1);
  assert(oct_value() == 519);
  assert(bin_value() == 15);
  return 0;
}
