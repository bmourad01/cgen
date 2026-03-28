#include <assert.h>

extern int foo(int x);

int
main() {
  assert(foo(0) == 0);
  assert(foo(5) == -1);
  assert(foo(-5) == 1);
  assert(foo(10) == -2);
  assert(foo(-10) == 2);
  assert(foo(100) == -20);
  assert(foo(-100) == 20);
  assert(foo(7) == -1);
  assert(foo(-7) == 1);
  assert(foo(3) == 0);
  assert(foo(-3) == 0);
  assert(foo(999) == (999 / -5));
  assert(foo(-999) == (-999 / -5));
}
