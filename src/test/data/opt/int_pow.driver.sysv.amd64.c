#include <assert.h>
#include <stdint.h>

extern int64_t int_pow(int64_t base, int64_t exponent);
extern int64_t int_pow_alt(int64_t base, int64_t exponent);

int
main() {
  assert(int_pow(2, 10) == 1024);
  assert(int_pow(5, 3) == 125);
  assert(int_pow(7, 0) == 1);
  assert(int_pow(7, 2) == 49);
  assert(int_pow(10, 3) == 1000);
  assert(int_pow(100, 2) == 10000);
  assert(int_pow(1, 9999) == 1);

  assert(int_pow_alt(2, 10) == 1024);
  assert(int_pow_alt(5, 3) == 125);
  assert(int_pow_alt(7, 0) == 1);
  assert(int_pow_alt(7, 2) == 49);
  assert(int_pow_alt(10, 3) == 1000);
  assert(int_pow_alt(100, 2) == 10000);
  assert(int_pow_alt(1, 9999) == 1);
}
