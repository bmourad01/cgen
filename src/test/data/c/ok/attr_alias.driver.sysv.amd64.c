#include <assert.h>

extern int aliased_fn(int);
extern int aliased_var;

int
main(void) {
  assert(aliased_fn(5) == 105);
  assert(aliased_fn(-100) == 0);
  assert(aliased_var == 42);
  return 0;
}
