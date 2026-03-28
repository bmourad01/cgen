#include <assert.h>

extern unsigned int foo(unsigned int x);

int
main() {
  assert(foo(0) == 0);
  assert(foo(8) == 1);
  assert(foo(16) == 2);
  assert(foo(7) == 0);
  assert(foo(15) == 1);
  assert(foo(100) == 12);
  assert(foo(999) == (999u / 8u));
  assert(foo(0xffffffff) == (0xffffffffu / 8u));
}
