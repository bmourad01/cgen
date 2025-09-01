#include <assert.h>

extern int foo(int n, int count);

int bar(int n) {
  return foo(n, 0);
}

int main() {
  assert(bar(1) == 0);
  assert(bar(2) == 1);
  assert(bar(3) == 7);
  assert(bar(4) == 2);
  assert(bar(5) == 5);
  assert(bar(6) == 8);
  assert(bar(7) == 16);
  assert(bar(8) == 3);
  assert(bar(9) == 19);
  assert(bar(10) == 6);
  return 0;
}
