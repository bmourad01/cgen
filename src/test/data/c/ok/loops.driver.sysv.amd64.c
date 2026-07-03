#include <assert.h>

extern int sum_odds(int n);
extern int count_down(int n);
extern int do_at_least_once(int n);
extern int do_count(int n);
extern int grid(int rows, int cols);

int
main(void) {
  assert(sum_odds(0) == 0);
  assert(sum_odds(1) == 0);
  assert(sum_odds(10) == 25);

  assert(count_down(0) == 0);
  assert(count_down(10) == 6);

  assert(do_at_least_once(0) == 1);
  assert(do_at_least_once(5) == 5);

  assert(do_count(8) == 6);
  assert(do_count(1) == 1);

  assert(grid(3, 4) == 9);
  assert(grid(0, 5) == 0);

  return 0;
}
