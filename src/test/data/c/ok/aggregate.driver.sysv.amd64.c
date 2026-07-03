#include <assert.h>

struct point {
  int x;
  int y;
};

extern struct point mkpoint(int x, int y);
extern int dot(struct point a, struct point b);
extern int sum_array(int *a, int n);

int
main(void) {
  struct point p = mkpoint(3, 4);
  assert(p.x == 3 && p.y == 4);

  struct point q = mkpoint(1, 2);
  assert(dot(p, q) == 3 * 1 + 4 * 2);

  int xs[5] = {10, 20, 30, 40, 50};
  assert(sum_array(xs, 5) == 150);
  assert(sum_array(xs, 0) == 0);
  assert(sum_array(xs + 2, 3) == 120);

  return 0;
}
