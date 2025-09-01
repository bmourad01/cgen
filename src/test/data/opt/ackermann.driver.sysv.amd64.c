#include <assert.h>

extern int foo(int m, int n);

int main() {
  assert(foo(0, 0) == 1);
  assert(foo(1, 3) == 5);
  assert(foo(2, 2) == 7);
  assert(foo(3, 2) == 29);
  return 0;
}
