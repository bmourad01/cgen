#include <assert.h>

extern unsigned int foo(unsigned int x);

int
main() {
  /* Divisor 641 used to make `Magic_div.unsigned` loop forever. */
  assert(foo(0) == 0);
  assert(foo(641) == 0);
  assert(foo(642) == 1);
  assert(foo(1282) == 0);
  assert(foo(1000000) == (1000000u % 641u));
  assert(foo(4294967295u) == (4294967295u % 641u));
  return 0;
}
