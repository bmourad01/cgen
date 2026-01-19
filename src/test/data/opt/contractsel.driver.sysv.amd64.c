#include <assert.h>

int foo(int x);

int
main() {
  assert(foo(43) == 5);
  assert(foo(100) == 5);
  assert(foo(-1) == 3);
  assert(foo(-42) == 3);
  assert(foo(0) == 0);
  assert(foo(1) == 1);
  assert(foo(42) == 42);
}
