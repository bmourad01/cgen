#include <assert.h>

extern unsigned int foo(unsigned int x);

int
main() {
  assert(foo(0) == 0);
  assert(foo(11) == 1);
  assert(foo(22) == 2);
  assert(foo(10) == 0);
  assert(foo(100) == 9);
  assert(foo(999) == (999u / 11u));
  assert(foo(0xffffffff) == (0xffffffffu / 11u));
}
