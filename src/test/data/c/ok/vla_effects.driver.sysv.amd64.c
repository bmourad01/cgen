#include <assert.h>

extern int cast_effect(void);
extern int sizeof_effect(void);
extern int alignof_no_effect(void);
extern int alignof_value(void);

int
main(void) {
  assert(cast_effect() == 2);
  assert(sizeof_effect() == 1);
  assert(alignof_no_effect() == 0);
  assert(alignof_value());
  return 0;
}
