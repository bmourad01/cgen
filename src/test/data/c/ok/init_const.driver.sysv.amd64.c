#include <assert.h>

extern unsigned long mask_of(int);
extern int third(void);
extern int matcher_elt(int, int);

int
main(void) {
  assert(mask_of(4) == 8);  /* 1 << 3 */
  assert(mask_of(5) == 32); /* 1 << 5 */
  assert(mask_of(6) == 40); /* (1<<3) | (1<<5) */
  assert(third() == 30);
  assert(matcher_elt(1, 0) == 1 && matcher_elt(1, 4) == 2 &&
         matcher_elt(1, 5) == 0);
  assert(matcher_elt(2, 0) == 9 && matcher_elt(2, 2) == 9);
  return 0;
}
