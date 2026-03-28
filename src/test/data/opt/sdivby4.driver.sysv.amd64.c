#include <assert.h>

extern int foo(int x);

int
main() {
  assert(foo(0) == 0);
  assert(foo(4) == 1);
  assert(foo(-4) == -1);
  assert(foo(7) == 1);
  assert(foo(-7) == -1);
  assert(foo(100) == 25);
  assert(foo(-100) == -25);
  assert(foo(1) == 0);
  assert(foo(-1) == 0);
}
