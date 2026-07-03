#include <assert.h>

extern int classify(int x);
extern int days_in_month(int m);
extern int accumulate(int n);

int
main(void) {
  assert(classify(0) == 1);
  assert(classify(1) == 1);
  assert(classify(2) == 2);
  assert(classify(7) == -1);
  assert(days_in_month(2) == 28);
  assert(days_in_month(4) == 30);
  assert(days_in_month(11) == 30);
  assert(days_in_month(1) == 31);
  assert(days_in_month(12) == 31);
  assert(accumulate(0) == 0);
  assert(accumulate(1) == 1);
  assert(accumulate(2) == 3);
  assert(accumulate(3) == 6);
  return 0;
}
