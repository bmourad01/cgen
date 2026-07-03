#include <assert.h>

extern int gcd(int a, int b);
extern int sumto(int n);
extern long fib(int n);

int
main(void) {
  assert(gcd(48, 36) == 12);
  assert(gcd(101, 103) == 1);
  assert(gcd(0, 7) == 7);
  assert(sumto(0) == 0);
  assert(sumto(10) == 55);
  assert(sumto(100) == 5050);
  assert(fib(0) == 0);
  assert(fib(1) == 1);
  assert(fib(10) == 55);
  assert(fib(20) == 6765);
  return 0;
}
