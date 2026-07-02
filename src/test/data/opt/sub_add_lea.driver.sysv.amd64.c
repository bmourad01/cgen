#include <assert.h>

extern long addr(long base, long idx);

int
main(void) {
  /* addr(b, i) must compute (b + i) - 16. */
  assert(addr(1000, 2000) == 2984);
  assert(addr(0, 0) == -16);
  assert(addr(100, 0) == 84);
  assert(addr(16, 0) == 0);
  return 0;
}
