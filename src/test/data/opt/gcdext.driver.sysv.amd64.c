#include <assert.h>

struct S {
  int gcd;
  int x;
  int y;
};

extern struct S gcd(int a, int b);

void test(int a, int b, int x) {
  struct S s = gcd(a, b);
  assert(s.gcd == x);
  assert(a * s.x + b * s.y == s.gcd);
}

int main() {
  test(12, 18, 6);
  test(30, 20, 10);
  test(101, 103, 1);
  test(0, 7, 7);
  test(7, 0, 7);
  test(18, 84, 6);
}
