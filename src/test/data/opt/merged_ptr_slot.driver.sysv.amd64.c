#include <assert.h>

extern int merged(int c);

int
main(void) {
  assert(merged(1) == 3);
  assert(merged(0) == 7);
  return 0;
}
