#include <assert.h>

extern int run(void);
extern int comma_void(void);

int
main(void) {
  assert(run() == 130);
  assert(comma_void() == 45);
  return 0;
}
