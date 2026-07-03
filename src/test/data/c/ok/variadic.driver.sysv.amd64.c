#include <assert.h>

struct P {
  int a;
  int b;
};

extern int sum(int n, ...);
extern double dsum(int n, ...);
extern int psum(int n, ...);
extern int sum3(int a, int b, int c);

int
main(void) {
  assert(sum(0) == 0);
  assert(sum(1, 42) == 42);
  assert(sum(4, 1, 2, 3, 4) == 10);
  assert(sum(8, 1, 2, 3, 4, 5, 6, 7, 8) == 36);
  assert(dsum(3, 1.5, 2.5, 3.0) == 7.0);
  assert(psum(2, (struct P){1, 2}, (struct P){3, 4}) == 10);
  assert(sum3(10, 20, 30) == 60);
  return 0;
}
