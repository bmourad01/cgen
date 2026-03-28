#include <assert.h>

extern int foo(int x);

int
main() {
  assert(foo(0) == 0);
  assert(foo(1) == 1);
  assert(foo(-1) == -1);
  assert(foo(100) == 100);
  assert(foo(-100) == -100);
  assert(foo(2147483647) == 2147483647);
  assert(foo(-2147483648) == -2147483648);
}
