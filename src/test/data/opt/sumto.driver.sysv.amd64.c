#include <assert.h>

extern int sumto(int n);

int
main(void) {
  assert(sumto(0) == 0);
  assert(sumto(1) == 1);
  assert(sumto(5) == 15);
  assert(sumto(10) == 55);
  assert(sumto(100) == 5050);
  return 0;
}
