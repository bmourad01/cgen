#include <assert.h>

extern int lastjoin(void);

int
main(void) {
  assert(lastjoin() == 0);
  return 0;
}
