#include <assert.h>

extern int selfref(void), array_sum(void), self_pointer(void);
extern unsigned long array_size(void);

int
main(void) {
  assert(selfref() == 1);
  assert(array_size() == 20);
  assert(array_sum() == 60);
  assert(self_pointer() == 21);
  return 0;
}
