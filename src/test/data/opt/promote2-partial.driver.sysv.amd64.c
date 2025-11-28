#include <assert.h>

extern int foo(int a, int b);

void
test(int a, int b, int x) {
  int gcd = foo(a, b);
  assert(gcd == x);
}

int
main() {
  test(12, 18, 6);
  test(30, 20, 10);
  test(101, 103, 1);
  test(0, 7, 7);
  test(7, 0, 7);
  test(18, 84, 6);
}
