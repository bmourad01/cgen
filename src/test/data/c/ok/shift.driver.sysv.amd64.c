#include <assert.h>

extern long shl(long a, int b);
extern long sar(long a, int b);
extern unsigned long shr(unsigned long a, int b);

int
main(void) {
  assert(shl(1L, 40) == 0x10000000000L);
  assert(sar(-1024L, 3) == -128L);
  assert(shr(0x8000000000000000UL, 4) == 0x0800000000000000UL);
  return 0;
}
