#include <assert.h>

extern unsigned int foo(unsigned int x);

int
main() {
  assert(foo(0) == 0);
  assert(foo(1) == 1);
  assert(foo(2) == 2);
  assert(foo(3) == 3);
  assert(foo(4) == 4);
  assert(foo(5) == 5);
  assert(foo(6) == 6);
  assert(foo(7) == 0);
  assert(foo(14) == 0);
  assert(foo(21) == 0);
  assert(foo(70) == 0);
  assert(foo(8) == 1);
  assert(foo(15) == 1);
  assert(foo(29) == 1);
  assert(foo(30) == 2);
  assert(foo(999) == (999u % 7u));
}
