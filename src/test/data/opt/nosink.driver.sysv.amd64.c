#include <assert.h>

extern int foo(int x);

int main() {
  assert(foo(0) == 0);
  assert(foo(1) == 9);
  assert(foo(2) == 15);
  assert(foo(3) == 20);
  assert(foo(4) == 25);
  assert(foo(5) == 30);
  assert(foo(-1) == 0);
  assert(foo(-2) == -5);
  assert(foo(10) == 55);
  assert(foo(100) == 505);
}
