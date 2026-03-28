#include <assert.h>

extern int foo(int x);

int
main() {
  assert(foo(0) == 0);
  assert(foo(1) == 1);
  assert(foo(2) == 0);
  assert(foo(-1) == -1);
  assert(foo(-2) == 0);
  assert(foo(3) == 1);
  assert(foo(-3) == -1);
  assert(foo(100) == 0);
  assert(foo(101) == 1);
  assert(foo(-101) == -1);
  assert(foo(999) == (999 % 2));
  assert(foo(-999) == (-999 % 2));
}
