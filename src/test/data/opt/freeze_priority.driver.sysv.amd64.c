#include <assert.h>

/* freeze_test(a, b, n, m) = 12*n*a + n*m*b */
extern int freeze_test(int a, int b, int n, int m);

int
main(void) {
  assert(freeze_test(0, 0, 0, 0) == 0);
  assert(freeze_test(1, 1, 1, 1) == 13);
  assert(freeze_test(1, 1, 3, 2) == 42);
  assert(freeze_test(2, 3, 5, 4) == 180);
  assert(freeze_test(10, 0, 7, 100) == 840); /* b = 0: only the phi-var term */
  assert(freeze_test(0, 5, 4, 6) == 120); /* a = 0: only the inner-loop term */
}
