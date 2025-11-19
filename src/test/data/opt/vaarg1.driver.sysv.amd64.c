#include <assert.h>

struct S {
  double d;
  long l;
};

extern long foo(long i, ...);

int main() {
  struct S s1 = {0.0, 1};
  assert(foo(1, s1) == 3);

  struct S s2 = {1.0, 1};
  assert(foo(1, s2) == 4);

  struct S s3 = {2.0, 5};
  assert(foo(10, s3) == 18);

  struct S s4 = {-2.5, 100};
  assert(foo(-4, s4) == 95);

  struct S s5 = {12.75, -20};
  assert(foo(0, s5) == -7);

  struct S s6 = {0.999, 0};
  assert(foo(1, s6) == 3);

  struct S s7 = {-0.1, 7};
  assert(foo(3, s7) == 11);

  struct S s8 = {-1.234, 42};
  assert(foo(0, s8) == 42);

  struct S s9 = {1000.5, 5000};
  assert(foo(1000, s9) == 7001);

  struct S s10 = {-100.9, -50};
  assert(foo(10, s10) == -139);
}
