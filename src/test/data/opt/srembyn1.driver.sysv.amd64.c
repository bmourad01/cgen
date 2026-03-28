#include <assert.h>

extern int foo(int x);

int
main() {
  assert(foo(0) == 0);
  assert(foo(1) == 0);
  assert(foo(-1) == 0);
  assert(foo(100) == 0);
  assert(foo(-100) == 0);
  assert(foo(2147483647) == 0);
}
