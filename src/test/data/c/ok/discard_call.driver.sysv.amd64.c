#include <assert.h>

extern int run(void);

int
main(void) {
  assert(run() == 130);
  return 0;
}
