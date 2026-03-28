#include <assert.h>

extern int foo(int x);

int
main() {
  assert(foo(0) == 0);
  assert(foo(8) == 0);
  assert(foo(-8) == 0);
  assert(foo(1) == 1);
  assert(foo(-1) == -1);
  assert(foo(9) == 1);
  assert(foo(-9) == -1);
  assert(foo(100) == 4);
  assert(foo(-100) == -4);
  assert(foo(999) == (999 % 8));
  assert(foo(-999) == (-999 % 8));
}
