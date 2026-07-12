#include <assert.h>
#include <stdint.h>

extern long g32[4];
extern char cbuf[8];
extern char adbl;
extern int local_aligned(void);

int
main(void) {
  assert((uintptr_t)g32 % 32 == 0);
  assert((uintptr_t)cbuf % 16 == 0);
  assert((uintptr_t)&adbl % _Alignof(double) == 0);
  assert(g32[0] == 1 && g32[3] == 4);
  assert(local_aligned() == 11);
  return 0;
}
