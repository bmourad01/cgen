#include <assert.h>

extern int compute(int x, int y);

int
main(void) {
  assert(compute(3, 4) == (3 + 4) + (3 * 4));    /* 7 + 12 = 19 */
  assert(compute(6, 7) == (6 + 7) + (6 * 7));    /* 13 + 42 = 55 */
  assert(compute(0, 9) == (0 + 9) + (0 * 9));    /* 9 + 0 = 9 */
  assert(compute(-2, 5) == (-2 + 5) + (-2 * 5)); /* 3 + -10 = -7 */
  return 0;
}
