#include <assert.h>

extern int eq_null(int *p);
extern int ne_null(int *p);
extern int null_eq(int *p);
extern int eq_voidnull(int *p);

int
main(void) {
  int x;
  assert(eq_null(0) == 1);
  assert(eq_null(&x) == 0);
  assert(ne_null(0) == 0);
  assert(ne_null(&x) == 1);
  assert(null_eq(0) == 1);
  assert(null_eq(&x) == 0);
  assert(eq_voidnull(0) == 1);
  assert(eq_voidnull(&x) == 0);
  return 0;
}
