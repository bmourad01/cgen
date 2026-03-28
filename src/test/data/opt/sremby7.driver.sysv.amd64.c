#include <assert.h>

extern int foo(int x);

int
main() {
  assert(foo(0) == 0);
  assert(foo(7) == 0);
  assert(foo(-7) == 0);
  assert(foo(1) == 1);
  assert(foo(-1) == -1);
  assert(foo(8) == 1);
  assert(foo(-8) == -1);
  assert(foo(100) == 2);
  assert(foo(-100) == -2);
  assert(foo(999) == (999 % 7));
  assert(foo(-999) == (-999 % 7));
}
