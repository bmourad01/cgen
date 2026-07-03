#include <assert.h>

extern int classify(int);
extern int interp(const int *);

int
main(void) {
  assert(classify(-5) == -1);
  assert(classify(0) == 0);
  assert(classify(7) == 1);

  /* acc = 10 + 5 - 3 = 12, then halt. */
  static const int prog[] = {0, 10, 0, 5, 1, 3, 2};
  assert(interp(prog) == 12);

  /* Halt immediately: acc stays 0. */
  static const int halt[] = {2};
  assert(interp(halt) == 0);

  return 0;
}
