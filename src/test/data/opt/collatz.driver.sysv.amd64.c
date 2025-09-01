#include <assert.h>

extern int foo(int n);

int main() {
  assert(foo(1) == 0);
  assert(foo(2) == 1);
  assert(foo(3) == 7);
  assert(foo(4) == 2);
  assert(foo(5) == 5);
  assert(foo(6) == 8);
  assert(foo(7) == 16);
  assert(foo(8) == 3);
  assert(foo(9) == 19);
  assert(foo(10) == 6);
  assert(foo(837799) == 524);
}
