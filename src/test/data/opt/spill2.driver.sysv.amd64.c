#include <assert.h>

extern int foo(int *a, int *b, int *c, int *d, int n);

int main() {
  int a0[] = {};
  int b0[] = {};
  int c0[] = {};
  int d0[] = {};
  assert(foo(a0, b0, c0, d0, 0) == 0);

  int a1[] = {0};
  int b1[] = {0};
  int c1[] = {0};
  int d1[] = {0};
  assert(foo(a1, b1, c1, d1, 1) == 0);

  int a2[] = {1};
  int b2[] = {2};
  int c2[] = {3};
  int d2[] = {4};
  assert(foo(a2, b2, c2, d2, 1) == 42);

  int a3[] = {1, 2};
  int b3[] = {3, 4};
  int c3[] = {5, 6};
  int d3[] = {7, 8};
  assert(foo(a3, b3, c3, d3, 2) == 368);

  int a4[] = {1, 1, 1};
  int b4[] = {1, 1, 1};
  int c4[] = {1, 1, 1};
  int d4[] = {1, 1, 1};
  assert(foo(a4, b4, c4, d4, 3) == 12);

  int a5[] = {1, 2, 3, 4, 5, 6, 7, 8, 9, 10};
  int b5[] = {2, 3, 4, 5, 6, 7, 8, 9, 10, 11};
  int c5[] = {3, 4, 5, 6, 7, 8, 9, 10, 11, 12};
  int d5[] = {4, 5, 6, 7, 8, 9, 10, 11, 12, 13};
  assert(foo(a5, b5, c5, d5, 10) == 17722);
}
