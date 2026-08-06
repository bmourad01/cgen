#include <assert.h>

extern long widen(int n, unsigned short s);

int
main(void) {
  assert(widen(1, 0U) == 5923454448935370888L);
  assert(widen(1, 1U) == 5923454448936419464L);
  assert(widen(1, 65535U) == 5923454517653799048L);
  assert(widen(3, 4660U) == 5923454453821735320L);
  assert(widen(10, 43981U) == 5923454495052793168L);
  assert(widen(64, 32768U) == 5923454483295117824L);
  assert(widen(1000, 32767U) == 5923454483294196544L);
  return 0;
}
