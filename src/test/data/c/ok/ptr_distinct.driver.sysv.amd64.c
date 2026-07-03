#include <assert.h>

extern int cross_assign(int x);
extern int deep_ne(signed char ***a, signed char ***b);

int
main(void) {
  assert(cross_assign(7) == 1);
  assert(cross_assign(-1) == 1);

  signed char c;
  signed char *p1 = &c;
  signed char **p2 = &p1;
  signed char **p2b = &p1;
  signed char ***x = &p2;
  signed char ***y = &p2;
  signed char ***z = &p2b;
  assert(deep_ne(x, y) == 0);
  assert(deep_ne(x, z) == 1);
  return 0;
}
